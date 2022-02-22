{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

-- Auxiliary module that gets stuff from 'Test.Ouroboros.Network.Server2'
-- and adapts them in order to be used in Diffusion Tests.
module Test.Ouroboros.Network.Testnet.Simulation.InboundGovernor where

import           Ouroboros.Network.ConnectionManager.Types
                     (Transition' (..))
import           Ouroboros.Network.InboundGovernor
                     (RemoteTransition, RemoteSt (..))

import           Test.QuickCheck
                     (Testable (property), counterexample)
import           Test.Ouroboros.Network.Testnet.Simulation.ConnectionManager
                     (AllProperty(..))


-- | Pattern synonym which matches either 'RemoteHotEst' or 'RemoteWarmSt'.
--
pattern RemoteEstSt :: RemoteSt
pattern RemoteEstSt <- (\ case
                            RemoteHotSt  -> True
                            RemoteWarmSt -> True
                            _            -> False -> True
                        )

-- | Specification of the transition table of the inbound governor.
--
verifyRemoteTransition :: RemoteTransition -> Bool
verifyRemoteTransition Transition {fromState, toState} =
    case (fromState, toState) of
      -- The initial state must be 'RemoteIdleSt'.
      (Nothing,           Just RemoteIdleSt) -> True

      --
      -- Promotions
      --

      (Just RemoteIdleSt, Just RemoteEstSt)  -> True
      (Just RemoteColdSt, Just RemoteEstSt)  -> True
      (Just RemoteWarmSt, Just RemoteHotSt)  -> True

      --
      -- Demotions
      --

      (Just RemoteHotSt,  Just RemoteWarmSt) -> True
      -- demotion to idle state can happen from any established state
      (Just RemoteEstSt,  Just RemoteIdleSt) -> True
      -- demotion to cold can only be done from idle state; We explicitly rule
      -- out demotions to cold from warm or hot states.
      (Just RemoteEstSt,  Just RemoteColdSt) -> False
      (Just RemoteIdleSt, Just RemoteColdSt) -> True
      -- normal termination (if outbound side is not using that connection)
      (Just RemoteIdleSt, Nothing)           -> True
      -- This transition corresponds to connection manager's:
      -- @
      --   Commit^{Duplex}_{Local} : OutboundIdleState Duplex
      --                           → TerminatingState
      -- @
      (Just RemoteColdSt, Nothing)           -> True
      -- any of the mini-protocols errored
      (Just RemoteEstSt, Nothing)            -> True

      --
      -- We are conservative to name all the identity transitions.
      --

      -- This might happen if starting any of the responders errored.
      (Nothing,           Nothing)           -> True
      -- @RemoteWarmSt → RemoteWarmSt@, @RemoteIdleSt → RemoteIdleSt@ and
      -- @RemoteColdSt → RemoteColdSt@ transition are observed if a hot or
      -- warm protocol terminates (which triggers @RemoteEstSt -> RemoteWarmSt@)
      (Just RemoteWarmSt, Just RemoteWarmSt) -> True
      (Just RemoteIdleSt, Just RemoteIdleSt) -> True
      (Just RemoteColdSt, Just RemoteColdSt) -> True

      (_,                 _)                 -> False


-- Assuming all transitions in the transition list are valid, we only need to
-- look at the 'toState' of the current transition and the 'fromState' of the
-- next transition.
verifyRemoteTransitionOrder :: [RemoteTransition]
                            -> AllProperty
verifyRemoteTransitionOrder [] = mempty
verifyRemoteTransitionOrder (h:t) = go t h
  where
    go :: [RemoteTransition] -> RemoteTransition -> AllProperty
    -- All transitions must end in the 'Nothing' (final) state, and since
    -- we assume all transitions are valid we do not have to check the
    -- 'fromState' .
    go [] (Transition _ Nothing) = mempty
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
