import TRZK.Pipeline

open TRZK

#guard optimize (.add (.var 0) (.const 0)) == some (.var 0)
#guard optimize (.add (.var 5) (.const 0)) == some (.var 5)
#guard optimize (.add (.const 0) (.var 0)) == some (.add (.const 0) (.var 0))
#guard optimize (.add (.add (.var 0) (.const 0)) (.const 0)) == some (.var 0)
#guard optimize (.add (.var 0) (.const 7)) == some (.add (.var 0) (.const 7))
#guard optimize (.const 0) == some (.const 0)
#guard optimize (.var 3) == some (.var 3)

#guard optimize (.mul (.var 0) (.const 1)) == some (.var 0)
#guard optimize (.mul (.var 5) (.const 1)) == some (.var 5)
#guard optimize (.mul (.const 1) (.var 0)) == some (.mul (.const 1) (.var 0))
#guard optimize (.mul (.mul (.var 0) (.const 1)) (.const 1)) == some (.var 0)
#guard optimize (.mul (.var 0) (.const 7)) == some (.mul (.var 0) (.const 7))
#guard optimize (.mul (.add (.var 0) (.const 0)) (.const 1)) == some (.var 0)
#guard optimize (.mul (.var 0) (.var 1)) == some (.mul (.var 0) (.var 1))

#guard optimize (.mul (.var 0) (.const 0)) == some (.const 0)
#guard optimize (.mul (.var 5) (.const 0)) == some (.const 0)

#guard optimize (.sub (.var 0) (.var 0)) == some (.const 0)
#guard optimize (.sub (.var 5) (.var 5)) == some (.const 0)
#guard optimize (.sub (.var 0) (.var 1)) == some (.sub (.var 0) (.var 1))
#guard optimize (.add (.sub (.var 0) (.var 0)) (.const 0)) == some (.const 0)

#guard optimize (.neg (.neg (.var 0))) == some (.var 0)
#guard optimize (.neg (.neg (.var 5))) == some (.var 5)
#guard optimize (.neg (.neg (.neg (.neg (.var 0))))) == some (.var 0)
#guard optimize (.neg (.var 0)) == some (.neg (.var 0))

-- New rule: x + (-x) → 0.
#guard optimize (.add (.var 0) (.neg (.var 0))) == some (.const 0)
#guard optimize (.add (.var 5) (.neg (.var 5))) == some (.const 0)
