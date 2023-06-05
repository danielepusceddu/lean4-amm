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

theorem 𝕋₁.other_in (m: 𝕋₁)
: m.other ∈ m.upair := by
unfold other; exact Sym2.other_mem (m.choose_in)

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

@[simp] theorem 𝕋₀.toMint_eq
{t0 t1 t0' t1': 𝕋₀}
{hdif1: t0 ≠ t1}
{hdif2: t0' ≠ t1'}
: 𝕋₀.toMint hdif1 = 𝕋₀.toMint hdif2 ↔ (t0 = t0' ∧ t1 = t1') ∨  (t0 = t1' ∧ t1 = t0') := by
  apply Iff.intro
  . intro minteq
    simp [𝕋₀.toMint, hdif1, hdif2] at minteq
    exact minteq
  
  . intro teq
    rcases teq with ⟨left,right⟩|⟨left,right⟩
    <;> simp [toMint, left, right]

theorem 𝕋₁.diff 
{m0 m1: 𝕋₁}
(hdif: m0 ≠ m1)
: (m0.choose ≠ m1.choose ∨ m0.other ≠ m1.other) ∧ (m0.choose ≠ m1.other ∨ m0.other ≠ m1.choose) := by
  rw [← 𝕋₁.choose_eq m0] at hdif
  rw [← 𝕋₁.choose_eq m1] at hdif
  have hdif' := 𝕋₀.toMint_diff hdif
  simp_rw [hdif']

theorem 𝕋₀.toMint_t0_cases
{t0 t1: 𝕋₀} (hdif: t0 ≠ t1):
(𝕋₀.toMint hdif).choose = t0 ∨ (𝕋₀.toMint hdif).choose = t1
:= by 
  unfold 𝕋₁.choose
  have hin:
   (Quotient.out (toMint hdif).upair).fst ∈ (toMint hdif).upair 
   := Sym2.out_fst_mem _
  simp only [𝕋₀.toMint]
  simp only [𝕋₀.toMint] at hin
  exact Sym2.mem_iff.mp hin

@[simp] theorem 𝕋₀.toMint_choose_t0_imp
{t0 t1: 𝕋₀} {hdif: t0 ≠ t1}
(hchoose: (𝕋₀.toMint hdif).choose = t0):
(𝕋₀.toMint hdif).other = t1
:= by 
  have hin1  := 𝕋₁.choose_in (𝕋₀.toMint hdif)
  have hin2  := 𝕋₁.other_in (𝕋₀.toMint hdif)
  have hdif' := (𝕋₀.toMint hdif).other_diff
  have hbruh := (Sym2.mem_and_mem_iff hdif').mp (And.intro hin1 hin2)
  simp [toMint] at hbruh
  rcases hbruh with ⟨_,left2⟩|⟨right1,right2⟩
  . simp [toMint]; symm; exact left2; 
  . simp [toMint] at hdif'
    simp [toMint] at hchoose
    conv at hchoose => rhs; rw [right1]
    contradiction

@[simp] theorem 𝕋₀.toMint_choose_t1_imp
(t0 t1: 𝕋₀) (hdif: t0 ≠ t1)
(hchoose: (𝕋₀.toMint hdif).choose = t1):
(𝕋₀.toMint hdif).other = t0
:= by 
  have hin1  := 𝕋₁.choose_in (𝕋₀.toMint hdif)
  have hin2  := 𝕋₁.other_in (𝕋₀.toMint hdif)
  have hdif' := (𝕋₀.toMint hdif).other_diff
  have hbruh := (Sym2.mem_and_mem_iff hdif').mp (And.intro hin1 hin2)
  simp [toMint] at hbruh
  rcases hbruh with ⟨left1,left2⟩|⟨right1,_⟩
  . simp [toMint] at hdif'
    simp [toMint] at hchoose
    conv at hchoose => rhs; rw [left2]
    contradiction
  . simp [toMint]; symm; exact right1; 

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