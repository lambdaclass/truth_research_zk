import TRZK.Pipeline

open TRZK

#guard optimize RuleSet.babybearNaive (.add (.var 0) (.const 0)) == some (.var 0)
#guard optimize RuleSet.babybearNaive (.add (.var 5) (.const 0)) == some (.var 5)
#guard optimize RuleSet.babybearNaive (.add (.const 0) (.var 0)) == some (.add (.const 0) (.var 0))
#guard optimize RuleSet.babybearNaive (.add (.add (.var 0) (.const 0)) (.const 0)) == some (.var 0)
#guard optimize RuleSet.babybearNaive (.add (.var 0) (.const 7)) == some (.add (.var 0) (.const 7))
#guard optimize RuleSet.babybearNaive (.const 0) == some (.const 0)
#guard optimize RuleSet.babybearNaive (.var 3) == some (.var 3)

#guard optimize RuleSet.babybearNaive (.mul (.var 0) (.const 1)) == some (.var 0)
#guard optimize RuleSet.babybearNaive (.mul (.var 5) (.const 1)) == some (.var 5)
#guard optimize RuleSet.babybearNaive (.mul (.const 1) (.var 0)) == some (.mul (.const 1) (.var 0))
#guard optimize RuleSet.babybearNaive (.mul (.mul (.var 0) (.const 1)) (.const 1)) == some (.var 0)
#guard optimize RuleSet.babybearNaive (.mul (.var 0) (.const 7)) == some (.mul (.var 0) (.const 7))
#guard optimize RuleSet.babybearNaive (.mul (.add (.var 0) (.const 0)) (.const 1)) == some (.var 0)
#guard optimize RuleSet.babybearNaive (.mul (.var 0) (.var 1)) == some (.mul (.var 0) (.var 1))

#guard optimize RuleSet.babybearNaive (.mul (.var 0) (.const 0)) == some (.const 0)
#guard optimize RuleSet.babybearNaive (.mul (.var 5) (.const 0)) == some (.const 0)

#guard optimize RuleSet.babybearNaive (.sub (.var 0) (.var 0)) == some (.const 0)
#guard optimize RuleSet.babybearNaive (.sub (.var 5) (.var 5)) == some (.const 0)
#guard optimize RuleSet.babybearNaive (.sub (.var 0) (.var 1)) == some (.sub (.var 0) (.var 1))
#guard optimize RuleSet.babybearNaive (.add (.sub (.var 0) (.var 0)) (.const 0)) == some (.const 0)

#guard optimize RuleSet.babybearNaive (.neg (.neg (.var 0))) == some (.var 0)
#guard optimize RuleSet.babybearNaive (.neg (.neg (.var 5))) == some (.var 5)
#guard optimize RuleSet.babybearNaive (.neg (.neg (.neg (.neg (.var 0))))) == some (.var 0)
#guard optimize RuleSet.babybearNaive (.neg (.var 0)) == some (.neg (.var 0))

-- New rule: x + (-x) → 0.
#guard optimize RuleSet.babybearNaive (.add (.var 0) (.neg (.var 0))) == some (.const 0)
#guard optimize RuleSet.babybearNaive (.add (.var 5) (.neg (.var 5))) == some (.const 0)
