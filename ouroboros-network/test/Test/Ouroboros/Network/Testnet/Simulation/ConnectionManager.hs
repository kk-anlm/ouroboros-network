{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}

module Test.Ouroboros.Network.Testnet.Simulation.ConnectionManager where

import           Control.Monad.IOSim (Trace)

import           Data.Maybe (fromJust, isJust)
import           Data.Bitraversable (bimapAccumL)
import           Data.List (find, dropWhileEnd)
import qualified Data.List.Trace as Trace
import qualified Data.Map as Map
import           Data.Monoid (Sum(..))

import           Text.Printf (printf)

import           Ouroboros.Network.ConnectionManager.Types
                     (AbstractTransition, Transition' (..), AbstractState (..),
                     Provenance (..), DataFlow (..), TimeoutExpired (..),
                     ConnectionManagerTrace (TrPruneConnections),
                     AbstractTransitionTrace, TransitionTrace' (..))
import           Ouroboros.Network.ConnectionHandler (ConnectionHandlerTrace)

import           Test.QuickCheck
                     (Property, (.&&.), Testable (property), label, tabulate,
                     cover, counterexample)

-- | Split 'AbstractTransitionTrace' into seprate connections.  This relies on
-- the property that every connection is terminated with 'UnknownConnectionSt'.
-- This property is verified by 'verifyAbstractTransitionOrder'.
--
splitConns :: Ord addr
           => (a -> AbstractTransitionTrace addr)
           -> Trace r a
           -> Trace r [a]
splitConns getTransition =
    fmap fromJust
  . Trace.filter isJust
  -- there might be some connections in the state, push them onto the 'Trace'
  . (\(s, o) -> foldr (\a as -> Trace.Cons (Just a) as) o (Map.elems s))
  . bimapAccumL
      ( \ s a -> (s, a))
      ( \ s a ->
          let TransitionTrace { ttPeerAddr, ttTransition } = getTransition a
           in case ttTransition of
             Transition _ UnknownConnectionSt ->
               case ttPeerAddr `Map.lookup` s of
                 Nothing  -> ( Map.insert ttPeerAddr [a] s
                             , Nothing
                             )
                 Just trs -> ( Map.delete ttPeerAddr s
                             , Just (reverse $ a : trs)
                             )
             _ ->            ( Map.alter ( \ case
                                               Nothing -> Just [a]
                                               Just as -> Just (a : as)
                                         ) ttPeerAddr s
                             , Nothing
                             )
      )
      Map.empty

verifyAbstractTransition :: AbstractTransition
                         -> Bool
verifyAbstractTransition Transition { fromState, toState } =
    case (fromState, toState) of
      --
      -- Outbound
      --

      -- @Reserve@
      (TerminatedSt, ReservedOutboundSt) -> True
      (UnknownConnectionSt, ReservedOutboundSt) -> True
      -- @Connected@
      (ReservedOutboundSt, UnnegotiatedSt Outbound) -> True
      -- @Negotiated^{Unidirectional}_{Outbound}@
      (UnnegotiatedSt Outbound, OutboundUniSt)  -> True
      -- @Negotiated^{Duplex}_{Outbound}@
      (UnnegotiatedSt Outbound, OutboundDupSt Ticking) -> True

      -- @DemotedToCold^{Unidirectional}_{Local}@
      (OutboundUniSt, OutboundIdleSt Unidirectional) -> True
      -- @TimeoutExpired@
      (OutboundDupSt Ticking, OutboundDupSt Expired) -> True
      -- @DemotedToCold^{Duplex}_{Local}@
      (OutboundDupSt Expired, OutboundIdleSt Duplex) -> True
      -- identity transition executed by 'demotedToColdRemote'
      (OutboundIdleSt dataFlow, OutboundIdleSt dataFlow') -> dataFlow == dataFlow'

      --
      -- Outbound ↔ Inbound
      --

      -- @DemotedToCold^{Duplex}_{Local}@
      (OutboundDupSt Ticking, InboundIdleSt Duplex) -> True
      -- @Awake^{Duplex}_{Local}
      (InboundIdleSt Duplex, OutboundDupSt Ticking) -> True
      -- @PromotedToWarm^{Duplex}_{Remote}@
      (OutboundDupSt Ticking, DuplexSt) -> True
      (OutboundDupSt Expired, DuplexSt) -> True
      -- can be executed by 'demotedToColdRemote'
      (OutboundDupSt expired, OutboundDupSt expired')
                                        -> expired == expired'
      -- @PromotedToWarm^{Duplex}_{Local}@
      (InboundSt Duplex, DuplexSt) -> True
      -- @DemotedToCold^{Duplex}_{Remote}@
      (DuplexSt, OutboundDupSt Ticking) -> True
      -- @DemotedToCold^{Duplex}_{Local}@
      (DuplexSt, InboundSt Duplex) -> True

      --
      -- Inbound
      --

      -- @Accepted@
      (TerminatedSt, UnnegotiatedSt Inbound) -> True
      (UnknownConnectionSt, UnnegotiatedSt Inbound) -> True
      -- @Overwritten@
      (ReservedOutboundSt, UnnegotiatedSt Inbound) -> True
      -- @Negotiated^{Duplex}_{Inbound}
      (UnnegotiatedSt Inbound, InboundIdleSt Duplex) -> True
      -- @Negotiated^{Unidirectional}_{Inbound}
      (UnnegotiatedSt Inbound, InboundIdleSt Unidirectional) -> True

      -- 'unregisterOutboundConnection' and 'demotedToColdRemote' might perfrom
      (InboundIdleSt Duplex, InboundIdleSt Duplex) -> True
      -- @Awake^{Duplex}_{Remote}
      (InboundIdleSt Duplex, InboundSt Duplex) -> True
      -- @Commit^{Duplex}
      (InboundIdleSt Duplex, TerminatingSt) -> True
      -- @DemotedToCold^{Duplex}_{Local}
      (InboundSt Duplex, InboundIdleSt Duplex) -> True

      -- @Awake^{Unidirectional}_{Remote}
      (InboundIdleSt Unidirectional, InboundSt Unidirectional) -> True
      -- @Commit^{Unidirectional}
      (InboundIdleSt Unidirectional, TerminatingSt) -> True
      -- @DemotedToCold^{Unidirectional}_{Local}
      (InboundSt Unidirectional, InboundIdleSt Unidirectional) -> True

      --
      -- OutboundIdleSt
      --

      (OutboundIdleSt Duplex, InboundSt Duplex) -> True
      (OutboundIdleSt _dataFlow, TerminatingSt) -> True

      --
      -- Terminate
      --

      -- @Terminate@
      (TerminatingSt, TerminatedSt) -> True

      -- explicit prohibition of reflexive terminate transition
      (TerminatedSt, TerminatedSt) -> False
      -- implicit terminate transition
      (_, TerminatedSt) -> True

      -- explicit prohibition of reflexive unknown transition
      (UnknownConnectionSt, UnknownConnectionSt) -> False
      (_, UnknownConnectionSt) -> True

      -- We accept connection in 'TerminatingSt'
      (TerminatingSt, UnnegotiatedSt Inbound) -> True

      _ -> False

-- Assuming all transitions in the transition list are valid, we only need to
-- look at the 'toState' of the current transition and the 'fromState' of the
-- next transition.
verifyAbstractTransitionOrder :: [AbstractTransition]
                              -> AllProperty
verifyAbstractTransitionOrder [] = mempty
verifyAbstractTransitionOrder (h:t) = go t h
  where
    go :: [AbstractTransition] -> AbstractTransition -> AllProperty
    -- All transitions must end in the 'UnknownConnectionSt', and since we
    -- assume that all transitions are valid we do not have to check the
    -- 'fromState'.
    go [] (Transition _ UnknownConnectionSt) = mempty
    go [] tr@(Transition _ _)          =
      AllProperty
        $ counterexample
            ("\nUnexpected last transition: " ++ show tr)
            (property False)
    -- All transitions have to be in a correct order, which means that the
    -- current state we are looking at (current toState) needs to be equal to
    -- the next 'fromState', in order for the transition chain to be correct.
    go (next@(Transition nextFromState _) : ts)
        curr@(Transition _ currToState) =
         AllProperty
           (counterexample
              ("\nUnexpected transition order!\nWent from: "
              ++ show curr ++ "\nto: " ++ show next)
              (property (currToState == nextFromState)))
         <> go ts next


--
-- | Test property together with classification.
--
data TestProperty = TestProperty {
    tpProperty            :: !Property,
    -- ^ 'True' if property is true

    tpNumberOfTransitions :: !(Sum Int),
    -- ^ number of all transitions

    tpNumberOfConnections :: !(Sum Int),
    -- ^ number of all connections

    tpNumberOfPrunings    :: !(Sum Int),
    -- ^ number of all connections

    --
    -- classification of connections
    --
    tpNegotiatedDataFlows :: ![NegotiatedDataFlow],
    tpEffectiveDataFlows  :: ![EffectiveDataFlow],
    tpTerminationTypes    :: ![TerminationType],
    tpActivityTypes       :: ![ActivityType],

    tpTransitions         :: ![AbstractTransition]

  }

instance Show TestProperty where
    show tp =
      concat [ "TestProperty "
             , "{ tpNumberOfTransitions = " ++ show (tpNumberOfTransitions tp)
             , ", tpNumberOfConnections = " ++ show (tpNumberOfConnections tp)
             , ", tpNumberOfPrunings = "    ++ show (tpNumberOfPrunings tp)
             , ", tpNegotiatedDataFlows = " ++ show (tpNegotiatedDataFlows tp)
             , ", tpTerminationTypes = "    ++ show (tpTerminationTypes tp)
             , ", tpActivityTypes = "       ++ show (tpActivityTypes tp)
             , ", tpTransitions = "         ++ show (tpTransitions tp)
             , "}"
             ]

instance Semigroup TestProperty where
  (<>) (TestProperty a0 a1 a2 a3 a4 a5 a6 a7 a8)
       (TestProperty b0 b1 b2 b3 b4 b5 b6 b7 b8) =
      TestProperty (a0 .&&. b0)
                   (a1 <> b1)
                   (a2 <> b2)
                   (a3 <> b3)
                   (a4 <> b4)
                   (a5 <> b5)
                   (a6 <> b6)
                   (a7 <> b7)
                   (a8 <> b8)

instance Monoid TestProperty where
    mempty = TestProperty (property True)
                          mempty mempty mempty mempty
                          mempty mempty mempty mempty

mkProperty :: TestProperty -> Property
mkProperty TestProperty { tpProperty
                        , tpNumberOfTransitions = Sum numberOfTransitions_
                        , tpNumberOfConnections = Sum numberOfConnections_
                        , tpNumberOfPrunings = Sum numberOfPrunings_
                        , tpNegotiatedDataFlows
                        , tpEffectiveDataFlows
                        , tpTerminationTypes
                        , tpActivityTypes
                        , tpTransitions
                        } =
     label (concat [ "Number of transitions: "
                   , within_ 10 numberOfTransitions_
                   ]
           )
   . label (concat [ "Number of connections: "
                   , show numberOfConnections_
                   ]
           )
   . tabulate "Pruning"             [show numberOfPrunings_]
   . tabulate "Negotiated DataFlow" (map show tpNegotiatedDataFlows)
   . tabulate "Effective DataFLow"  (map show tpEffectiveDataFlows)
   . tabulate "Termination"         (map show tpTerminationTypes)
   . tabulate "Activity Type"       (map show tpActivityTypes)
   . tabulate "Transitions"         (map ppTransition tpTransitions)
   $ tpProperty

mkPropertyPruning :: TestProperty -> Property
mkPropertyPruning tp@TestProperty { tpNumberOfPrunings = Sum numberOfPrunings_ } =
     cover 35 (numberOfPrunings_ > 0) "Prunings"
   . mkProperty
   $ tp

newtype AllProperty = AllProperty { getAllProperty :: Property }

instance Semigroup AllProperty where
    AllProperty a <> AllProperty b = AllProperty (a .&&. b)

instance Monoid AllProperty where
    mempty = AllProperty (property True)

data ActivityType
    = IdleConn

    -- | Active connections are onces that reach any of the state:
    --
    -- - 'InboundSt'
    -- - 'OutobundUniSt'
    -- - 'OutboundDupSt'
    -- - 'DuplexSt'
    --
    | ActiveConn
    deriving (Eq, Show)

data TerminationType
    = ErroredTermination
    | CleanTermination
    deriving (Eq, Show)

data NegotiatedDataFlow
    = NotNegotiated

    -- | Negotiated value of 'DataFlow'
    | NegotiatedDataFlow DataFlow
    deriving (Eq, Show)

data EffectiveDataFlow
    -- | Unlike the negotiated 'DataFlow' this indicates if the connection has
    -- ever been in 'DuplexSt'
    --
    = EffectiveDataFlow DataFlow
    deriving (Eq, Show)


-- classify negotiated data flow
classifyPrunings :: [ConnectionManagerTrace
                      addr
                      (ConnectionHandlerTrace v d)]
                 -> Sum Int
classifyPrunings =
  Sum
  . length
  . filter ( \ tr
             -> case tr of
                  x -> case x of
                    TrPruneConnections _ _ _ -> True
                    _                        -> False
           )

-- classify negotiated data flow
classifyNegotiatedDataFlow :: [AbstractTransition] -> NegotiatedDataFlow
classifyNegotiatedDataFlow as =
  case find ( \ tr
             -> case toState tr of
                  OutboundUniSt    -> True
                  OutboundDupSt {} -> True
                  InboundIdleSt {} -> True
                  _                -> False
            ) as of
     Nothing -> NotNegotiated
     Just tr ->
       case toState tr of
         OutboundUniSt      -> NegotiatedDataFlow Unidirectional
         OutboundDupSt {}   -> NegotiatedDataFlow Duplex
         (InboundIdleSt df) -> NegotiatedDataFlow df
         _                  -> error "impossible happened!"

-- classify effective data flow
classifyEffectiveDataFlow :: [AbstractTransition] -> EffectiveDataFlow
classifyEffectiveDataFlow as =
  case find ((== DuplexSt) . toState) as of
    Nothing -> EffectiveDataFlow Unidirectional
    Just _  -> EffectiveDataFlow Duplex

-- classify termination
classifyTermination :: [AbstractTransition] -> TerminationType
classifyTermination as =
      -- as might be empty in Diffusion tests
  let as' = Transition UnknownConnectionSt UnknownConnectionSt : as
   in case last $ dropWhileEnd
                    (== (Transition TerminatedSt TerminatedSt))
                $ dropWhileEnd
                    (== (Transition TerminatedSt UnknownConnectionSt))
                $ as' of
        Transition { fromState = TerminatingSt
                   , toState   = TerminatedSt
                   } -> CleanTermination
        _            -> ErroredTermination

-- classify if a connection is active or not
classifyActivityType :: [AbstractTransition] -> ActivityType
classifyActivityType as =
  case find ( \ tr
             -> case toState tr of
                  InboundSt     {} -> True
                  OutboundUniSt    -> True
                  OutboundDupSt {} -> True
                  DuplexSt      {} -> True
                  _                -> False
            ) as of
    Nothing -> IdleConn
    Just {} -> ActiveConn

ppTransition :: AbstractTransition -> String
ppTransition Transition {fromState, toState} =
    printf "%-30s → %s" (show fromState) (show toState)

within_ :: Int -> Int -> String
within_ _ 0 = "0"
within_ a b = let x = b `div` a in
              concat [ if b < a
                         then "1"
                         else show $ x * a
                     , " - "
                     , show $ x * a + a - 1
                     ]
