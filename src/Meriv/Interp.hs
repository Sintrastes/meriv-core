
module Meriv.Interp where

import Meriv.Types

type SearchTree m v t g = Tree (MvGoal m v t g) [] (Solution m v t)

-- | Construct a search tree from a set of rules and a goal.
search :: _ => Rules v t m (VoidF v t) -> Goal v t m (VoidF v t) -> m (SearchTree v t m (VoidF v t))
search program goal = return $ go program goal (Assignments [])
  where 
    -- When our goal is exhausted, we can return a solution.
    go (Rules !clauses) (Goal []) (Assignments !assignments) = trace "leaf" $
        Leaf $ Solution $ assignments <&> (\(var, y) -> 
          -- All variables will be ground at the end of the search
          -- procedure, since the goal (which contains free variables)
          -- will be empty
          let term = fromJust_UNSAFE $ groundSome y in
          -- At the end of the search procedure we evaluate all expressions
          -- to normal form.
          let evaluatedTerm = trace "Evaluating expression" $ evaluateSomeExpr term in
          
          (var, evaluatedTerm)
        ) 
    -- If there are still terms left in the goal, we branch on 
    -- the different possibilities for resolving the goal.
    go (Rules !clauses) (Goal goal@(t : ts)) (Assignments !assgn) = trace "In branch" $ Branch (Goal goal) trees
      where 
        varsInGoal = join $ map variables goal
        trees = do
          clause <- clauses
          let Clause !clauseHead !clauseBody = freshen varsInGoal clause
          trace (show $ evaluateTermIfGround t) $ return ()
          case unify clauseHead (evaluateTermIfGround t) of
            -- If it unifies, make the appropriate substitution and continue.
            Just !unifier -> do
              let newGoal = Goal $ map (subsTerm unifier) $ clauseBody <> ts
              let newAssignments = Assignments $ assgn <> unifier
              return $ go program newGoal newAssignments
            -- Otherwise, this branch is empty.
            Nothing -> trace "does not unify" $ mempty

    fromJust_UNSAFE (Just x) = x
