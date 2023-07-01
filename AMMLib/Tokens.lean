import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Finsupp.Basic
import HelpersLib.PReal
import HelpersLib.Finsupp2
open BigOperators

structure 𝔸 where
  n: ℕ

structure 𝕋₀ where
  n: ℕ

instance: DecidableEq 𝔸 := 
  fun a1 a2 => by 
  cases a1; cases a2; simp; infer_instance

instance: DecidableEq 𝕋₀ := 
  fun a1 a2 => by 
  cases a1; cases a2; simp; infer_instance

abbrev AtomicOracle  := 𝕋₀ → PReal

def diffpair (t0 t1 t0' t1': 𝕋₀): Prop :=
  (t0 ≠ t0' ∧ t1 ≠ t1') ∨ (t0 ≠ t1' ∨ t1 ≠ t0')

instance (t0 t1 t0' t1': 𝕋₀): Decidable (diffpair t0 t1 t0' t1') := 
  by sorry