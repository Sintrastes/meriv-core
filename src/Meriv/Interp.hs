
module Meriv.Interp where

import Meriv.Types
import Meriv.Util.Functor
import Control.Unification
import Control.Monad.Tree
import Control.Monad
import Data.Functor
import Debug.Trace

newtype MvSolution v s (e :: MvType s -> *)
  = MvSolution [(v, SomeGroundMvTerm s e)]

newtype Assignments v s (e :: MvType s -> *) = Assignments [(v, SomeMvTerm (VarT v) s e)]

type SearchTree v s (e :: MvType s -> *) = Tree (MvGoal v s e) [] (MvSolution v s e)

-- | Construct a search tree from a set of rules and a goal.
search :: _ => MvRules v s e -> MvGoal v s e -> SearchTree v s e
search program goal = go program goal (Assignments [])
  where 
    -- When our goal is exhausted, we can return a solution.
    go (MvRules !clauses) (MvGoal []) (Assignments !assignments) = trace "leaf" $
        Leaf $ MvSolution $ assignments <&> (\(var, y) -> 
          -- All variables will be ground at the end of the search
          -- procedure, since the goal (which contains free variables)
          -- will be empty
          let term = fromJust_UNSAFE $ groundSome y in
          -- At the end of the search procedure we evaluate all expressions
          -- to normal form.
          -- let evaluatedTerm = trace "Evaluating expression" $ evaluateSomeExpr term in
          
          (var, term)
        ) 
    -- If there are still terms left in the goal, we branch on 
    -- the different possibilities for resolving the goal.
    go (MvRules !clauses) (MvGoal goal@(t : ts)) (Assignments !assgn) = trace "In branch" $ Node (MvGoal goal) trees
      where 
        varsInGoal = join $ map variables goal
        trees = do
          clause <- clauses
          let MvClause !clauseHead !clauseBody = freshen varsInGoal clause
          -- trace (show $ evaluateTermIfGround t) $ return ()
          -- Functional evaluation not currently supported
          case unify clauseHead t of
            -- If it unifies, make the appropriate substitution and continue.
            Just !(SomeMvUnifier unifier) -> do
              let newGoal = MvGoal $
	            map (\(SomeMvTerm x) -> SomeMvTerm $
	                    subs (MvUnifier unifier) x
	                ) $
	            clauseBody <> ts
              let newAssignments = Assignments $ assgn <> unifier
              return $ go program newGoal newAssignments
            -- Otherwise, this branch is empty.
            Nothing -> trace "does not unify" $ mempty

    fromJust_UNSAFE (Just x) = x
