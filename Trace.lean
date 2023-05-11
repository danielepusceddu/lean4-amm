import «Deposit»
import «State»
import «Tokens»
import «Swap»

inductive Trace (c: Config): State → Type where
  | empty (accs: AccountSet): 
      Trace c ⟨accs, AMMSet.empty⟩

  | dep0 (rs: Trace c s) (d: Deposit0.Valid s): 
      Trace c (Deposit0.apply d)

  | swap (rs: Trace c s) (sw: Swap.Valid c s):
      Trace c (Swap.apply sw)

