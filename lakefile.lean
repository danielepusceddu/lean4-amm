import Lake
open Lake DSL

package «lean4-amm» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"


lean_lib AMMSet {
  -- add any library configuration options here
}

lean_lib Helpers {
  -- add any library configuration options here
}

lean_lib PReal {
  -- add any library configuration options here
}

@[default_target]
lean_lib Swap {
  -- add any library configuration options here
}

lean_lib State {
  -- add any library configuration options here
}

lean_lib Trace {
  -- add any library configuration options here
}

lean_lib Deposit {
  -- add any library configuration options here
}

lean_lib Finsupp2 {
  -- add any library configuration options here
}

lean_lib Supply {
  -- add any library configuration options here
}

lean_lib Tokens {
  -- add any library configuration options here
}

