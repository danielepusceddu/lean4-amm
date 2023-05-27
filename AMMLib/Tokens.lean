import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Finsupp.Basic
import AMMLib.PReal
import AMMLib.Helpers
import AMMLib.Finsupp2
open BigOperators

structure Account where
  n: ℕ

structure 𝕋₀ where
  n: ℕ

instance: DecidableEq Account := 
  fun a1 a2 => by 
  cases a1; cases a2; simp; infer_instance

instance: DecidableEq 𝕋₀ := 
  fun a1 a2 => by 
  cases a1; cases a2; simp; infer_instance

structure 𝕋₁ where
  upair: Sym2 𝕋₀
  hdiff: ¬Sym2.IsDiag upair

def 𝕋₀.toMint
{t0 t1: 𝕋₀} (hdif: t0 ≠ t1): 𝕋₁ :=
⟨
  Quotient.mk (Sym2.Rel.setoid 𝕋₀) (t0, t1),
  by simp [hdif]
⟩

noncomputable def 𝕋₁.choose (m: 𝕋₁)
: 𝕋₀
:= (Quotient.out m.upair).fst

theorem 𝕋₁.choose_in (m: 𝕋₁)
: m.choose ∈ m.upair := by
unfold choose; exact Sym2.out_fst_mem m.upair

noncomputable def 𝕋₁.other (m: 𝕋₁)
: 𝕋₀
:= Sym2.Mem.other (𝕋₁.choose_in m)

theorem 𝕋₁.other_diff (m: 𝕋₁)
: m.choose ≠ m.other := by
unfold other
exact (Sym2.other_ne m.hdiff m.choose_in).symm

theorem 𝕋₁.eq_iff 
(m1: 𝕋₁) (m2: 𝕋₁)
: m1 = m2 ↔ m1.upair = m2.upair := by
apply Iff.intro
. intro h; simp [h]
. intro h; cases m1; cases m2; simp at h; simp [h]

@[simp] theorem 𝕋₁.choose_eq (m: 𝕋₁)
: 𝕋₀.toMint (m.other_diff) = m := by
simp [𝕋₀.toMint]
apply (𝕋₁.eq_iff _ _).mpr
simp [choose, other]

instance: DecidableEq 𝕋₁ :=
  fun x y => 
  by rcases x with ⟨p1,h1⟩
     rcases y with ⟨p2,h2⟩
     simp
     infer_instance

theorem 𝕋₀.toMint_diff 
{t0 t1 t0' t1': 𝕋₀}
{hdif1: t0 ≠ t1}
{hdif2: t0' ≠ t1'}
(hdif3: 𝕋₀.toMint hdif1 ≠ 𝕋₀.toMint hdif2)
: (t0 ≠ t0' ∨ t1 ≠ t1') ∧ (t0 ≠ t1' ∨ t1 ≠ t0') := by
  simp [𝕋₀.toMint, hdif1, hdif2] at hdif3
  rcases (not_or.mp hdif3) with ⟨left, right⟩
  have left' := not_and_or.mp left
  have right' := not_and_or.mp right
  exact And.intro left' right'



abbrev Wall0 := Account →₀ 𝕋₀ →₀ NNReal
abbrev Wall1 := Account →₀ 𝕋₁ →₀ NNReal
abbrev AtomicOracle  := 𝕋₀ → PReal

noncomputable def Wall0.addb (as: Wall0) (a: Account) (t: 𝕋₀) (v: NNReal)
  : Wall0 := as.up a t ((as a t) + v)

noncomputable def Wall0.subb (as: Wall0) (a: Account) (t: 𝕋₀) (v: NNReal)
  : Wall0 := as.up a t ((as a t) - v)

noncomputable def Wall1.addb (as: Wall1) (a: Account) (t: 𝕋₁) (v: NNReal)
  : Wall1 := as.up a t ((as a t) + v)

noncomputable def Wall1.subb (as: Wall1) (a: Account) (t: 𝕋₁) (v: NNReal)
  : Wall1 := as.up a t ((as a t) - v)