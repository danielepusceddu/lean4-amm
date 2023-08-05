import HelpersLib.PReal.Basic
import HelpersLib.PReal.Order
import HelpersLib.PReal.Subtraction

abbrev SX := PReal → PReal → PReal → PReal

noncomputable def SX.constprod: SX := 
  λ (x r0 r1: ℝ+) => r1/(r0 + x)

/-
START
p0 / p1 ≤ r1 / (r0 + x)

p1/p0 ≥ (r0+x)/r1                          inversion
(r0+x)/r1 ≤ p1/p0                          side switch
r0/r1 + x/r1 ≤ p1/p0                       div of sum
r0/r1 < r0/r1 + x/r1 ≤ p1/p0               by positivity
r0/(r1+y) < r0/r1 < r0/r1 + x/r1 ≤ p1/p0   by greater denumerator

GOAL
r0 / (r1 + y) < p1 / p0                 by transitivity
-/
theorem SX.lemma61_constprod
  (x r0 r1 p0 p1: ℝ+)
  (h: p0/p1 ≤ constprod x r0 r1):
  ∀ (y: ℝ+), constprod y r1 r0 < p1/p0 := by
  intro y
  unfold constprod at h ⊢

  rw [← inv_div p1 p0] at h
  rw [← inv_div (r0+x) r1] at h
  simp only [inv_le_inv_iff] at h
  rw [PReal.add_div'' r0 x r1] at h

  simp only [← gt_iff_lt]
  calc
    p1/p0 ≥ r0/r1 + x/r1 := ge_iff_le.mpr h
    _     > r0/r1        := PReal.gt_add_right _ _
    _     > r0/(r1+y)    := PReal.div_lt_add_denum _ _ _

def SX.outputbound (sx: SX): Prop :=
  ∀ (x r0 r1: ℝ+),
     x*(sx x r0 r1) < r1

def SX.mono (sx: SX): Prop :=
∀ (x r0 r1 x' r0' r1': ℝ+),
  x' ≤ x ∧ r0' ≤ r0 ∧ r1' ≤ r1
  →
  sx x r0 r1 ≤ sx x' r0' r1'

def SX.strictmono (sx: SX): Prop :=
∀ (x r0 r1 x' r0' r1': ℝ+),
  x' ≤ x ∧ r0' ≤ r0 ∧ r1' ≤ r1
  →
  if x' < x ∨ r0' < r0 ∨ r1' < r1
  then sx x r0 r1 < sx x' r0' r1'
  else sx x r0 r1 ≤ sx x' r0' r1'

def SX.homogeneous (sx: SX): Prop :=
∀ (a x r0 r1: ℝ+), sx (a*x) (a*r0) (a*r1) = sx x r0 r1
