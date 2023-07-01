import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Sym.Sym2
import Mathlib.Algebra.BigOperators.Finsupp
import HelpersLib.NNReal
import HelpersLib.Prod
import HelpersLib.PReal
import HelpersLib.Finsupp2
import AMMLib.Tokens

structure 𝕎₁ where 
  f: 𝕋₀ →₀ 𝕋₀ →₀ NNReal
  h1: ∀ (t0 t1: 𝕋₀), f t0 t1 = f t1 t0
  h2: ∀ (t: 𝕋₀), f t t = 0

def 𝕎₁.empty: 𝕎₁ :=
⟨ 
  0,
  by simp,
  by simp
⟩

instance: Zero 𝕎₁ := ⟨𝕎₁.empty⟩

def 𝕎₁.get (w: 𝕎₁) (t0 t1: 𝕋₀): NNReal := w.f t0 t1

theorem 𝕎₁.get_reorder (w: 𝕎₁) (t1 t0: 𝕋₀):
  w.get t1 t0 = w.get t0 t1 := by
  simp [w.h1, 𝕎₁.get]

def 𝕎₁.add (w: 𝕎₁) (t0 t1: 𝕋₀) (hdif: t0 ≠ t1) (x: NNReal): 𝕎₁ := by sorry

theorem W₁.add_reorder (w: 𝕎₁) (t1 t0: 𝕋₀) (hdif: t0 ≠ t1) (x: NNReal):
  w.add t1 t0 hdif.symm x = w.add t0 t1 hdif x := by sorry

@[simp] theorem 𝕎₁.get_add_self (w: 𝕎₁) (t0 t1: 𝕋₀) (hdif: t0 ≠ t1) (x: NNReal):
  (w.add t0 t1 hdif x).get t0 t1 = w.get t0 t1 + x := by sorry

@[simp] theorem 𝕎₁.get_add_diff (w: 𝕎₁) (t0 t1: 𝕋₀) (hdif: t0 ≠ t1) (x: NNReal) (t0' t1': 𝕋₀) (diffp: diffpair t0 t1 t0' t1'):
  (w.add t0 t1 hdif x).f t0' t1' = w.get t0' t1' := by sorry

def 𝕎₁.sub (w: 𝕎₁) (t0 t1: 𝕋₀) (hdif: t0 ≠ t1) (x: NNReal) (h: x ≤ w.get t0 t1): 𝕎₁ := by sorry

theorem W₁.sub_reorder (w: 𝕎₁) (t1 t0: 𝕋₀) (hdif: t0 ≠ t1) (x: NNReal) (h: x ≤ w.get t0 t1):
  w.sub t1 t0 hdif.symm x (by sorry) = w.sub t0 t1 hdif x h := by sorry

@[simp] theorem 𝕎₁.get_sub_self (w: 𝕎₁) (t0 t1: 𝕋₀) (hdif: t0 ≠ t1) (x: NNReal) (h: x ≤ w.get t0 t1):
  (w.sub t0 t1 hdif x h).f t0 t1 = w.get t0 t1 - x := by sorry

@[simp] theorem 𝕎₁.get_sub_diff (w: 𝕎₁) (t0 t1: 𝕋₀) (hdif: t0 ≠ t1) (x: NNReal) (h: x ≤ w.get t0 t1) (t0' t1': 𝕋₀) (diffp: diffpair t0 t1 t0' t1'):
  (w.sub t0 t1 hdif x h).f t0' t1' = w.get t0' t1' := by sorry

def 𝕎₁.drain (w: 𝕎₁) (t0 t1: 𝕋₀) (hdif: t0 ≠ t1): 𝕎₁ := 
  w.sub t0 t1 hdif (w.get t0 t1) (by simp)

theorem W₁.drain_reorder (w: 𝕎₁) (t1 t0: 𝕋₀) (hdif: t0 ≠ t1):
  w.drain t1 t0 hdif.symm = w.drain t0 t1 hdif := by sorry

@[simp] theorem W₁.get_drain_self (w: 𝕎₁) (t0 t1: 𝕋₀) (hdif: t0 ≠ t1):
  (w.drain t0 t1 hdif).f t0 t1 = 0 := by sorry

@[simp] theorem 𝕎₁.get_drain_diff (w: 𝕎₁) (t0 t1: 𝕋₀) (hdif: t0 ≠ t1) (t0' t1': 𝕋₀) (diffp: diffpair t0 t1 t0' t1'):
  (w.drain t0 t1 hdif).f t0' t1' = w.get t0' t1' := by sorry

def test' (o: 𝕋₀ → 𝕋₀ → NNReal) (t0 t1: 𝕋₀) (x: NNReal): NNReal := x*(o t0 t1)

def test (o: 𝕋₀ → 𝕋₀ → NNReal) (t0: 𝕋₀) (b: 𝕋₀ →₀ NNReal): NNReal := 
  Finsupp.sum b (test' o t0)

def 𝕎₁.worth (w: 𝕎₁) (o: 𝕋₀ → 𝕋₀ → NNReal): NNReal :=
  w.f.sum (test o)

def 𝕎₁.worth_destruct (w: 𝕎₁) (o: 𝕋₀ → 𝕋₀ → NNReal) (t0 t1: 𝕋₀) (hdif: t0 ≠ t1):
  w.worth o = (w.drain t0 t1 hdif).worth o + (w.get t0 t1)*(o t0 t1)
  := by sorry