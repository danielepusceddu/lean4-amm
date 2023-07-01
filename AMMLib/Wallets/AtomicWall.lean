import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Sym.Sym2
import Mathlib.Algebra.BigOperators.Finsupp
import HelpersLib.NNReal
import HelpersLib.Prod
import HelpersLib.PReal
import HelpersLib.Finsupp2
import AMMLib.Tokens

abbrev 𝕎₀ := 𝕋₀ →₀ NNReal

def 𝕎₀.add (w: 𝕎₀) (t: 𝕋₀) (x: NNReal): 𝕎₀ := by sorry

@[simp] theorem 𝕎₀.get_add_self (w: 𝕎₀) (t: 𝕋₀) (x: NNReal):
  (w.add t x) t = w t + x := by sorry

@[simp] theorem 𝕎₀.get_add_diff (w: 𝕎₀) (t: 𝕋₀) (x: NNReal) (t': 𝕋₀) (hdif: t ≠ t'):
  (w.add t x) t' = w t' := by sorry

def 𝕎₀.sub (w: 𝕎₀) (t: 𝕋₀) (x: NNReal) (h: x ≤ w t): 𝕎₀ := by sorry

@[simp] theorem 𝕎₀.get_sub_self (w: 𝕎₀) (t: 𝕋₀) (x: NNReal) (h: x ≤ w t):
  (w.sub t x h) t = w t - x := by sorry

@[simp] theorem 𝕎₀.get_sub_diff (w: 𝕎₀) (t: 𝕋₀) (x: NNReal) (h: x ≤ w t) (t': 𝕋₀) (diff: t ≠ t'):
  (w.sub t x h) t' = w t' := by sorry

def 𝕎₀.drain (w: 𝕎₀) (t: 𝕋₀): 𝕎₀ := 
  w.sub t (w t) (by simp)

theorem 𝕎₀.get_drain_self (w: 𝕎₀) (t: 𝕋₀):
  (w.drain t) t = 0 := by sorry

theorem 𝕎₀.drain_comm (w: 𝕎₀) (t0 t1: 𝕋₀):
  (w.drain t1).drain t0 = (w.drain t0).drain t1 := by sorry

@[simp] theorem 𝕎₀.get_drain_diff (w: 𝕎₀) (t t': 𝕋₀) (diffp: t ≠ t'):
  (w.drain t) t' = w t' := by sorry

@[simp] theorem 𝕎₀.drain_add_self (w: 𝕎₀) (t: 𝕋₀) (x: NNReal):
  (w.add t x).drain t = w.drain t := by sorry

@[simp] theorem 𝕎₀.drain_sub_self (w: 𝕎₀) (t: 𝕋₀) (x: NNReal) (h: x ≤ w t):
  (w.sub t x h).drain t = w.drain t := by sorry

@[simp] theorem 𝕎₀.drain_add_diff (w: 𝕎₀) (t: 𝕋₀) (x: NNReal) (t': 𝕋₀) (hdif: t ≠ t'):
  (w.add t x).drain t' = (w.drain t').add t x := by sorry

@[simp] theorem 𝕎₀.drain_sub_diff (w: 𝕎₀) (t: 𝕋₀) (x: NNReal) (h: x ≤ w t) (t': 𝕋₀) (hdif: t ≠ t'):
  (w.sub t x h).drain t' = (w.drain t').sub t x (by simp[h,hdif.symm]) := by sorry

def 𝕎₀.worth (w: 𝕎₀) (o: 𝕋₀ → PReal): NNReal :=
  w.sum (λ t x => x*(o t))

theorem 𝕎₀.worth_destruct (w: 𝕎₀) (o: 𝕋₀ → PReal) (t: 𝕋₀):
  w.worth o = (w.drain t).worth o + (w t)*(o t)
  := by sorry

@[simp] theorem 𝕎₀.worth_add_destruct (w: 𝕎₀) (t: 𝕋₀) (x: NNReal) (o: 𝕋₀ → PReal):
  ((w.add t x).drain t).worth o = (w.drain t).worth o
  := by sorry

@[simp] theorem 𝕎₀.worth_sub_destruct (w: 𝕎₀) (t: 𝕋₀) (x: NNReal) (h: x ≤ w t) (o: 𝕋₀ → PReal):
  ((w.sub t x h).drain t).worth o = (w.drain t).worth o
  := by sorry