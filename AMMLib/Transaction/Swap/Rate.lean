import HelpersLib.PReal.Basic
import HelpersLib.PReal.Order
import HelpersLib.PReal.Subtraction

abbrev SX := ℝ>0 → ℝ>0 → ℝ>0 → ℝ>0
/-
abbrev SX := ℝ>0 → ℝ>0 → ℝ>0 → ℝ>0
-/

def SX.outputbound (sx: SX): Prop :=
  ∀ (x r0 r1: ℝ>0),
     x*(sx x r0 r1) < r1

def SX.mono (sx: SX): Prop :=
∀ (x r0 r1 x' r0' r1': ℝ>0),
  x' ≤ x ∧ r0' ≤ r0 ∧ r1' ≤ r1
  →
  sx x r0 r1 ≤ sx x' r0' r1'

def SX.strictmono (sx: SX): Prop :=
∀ (x r0 r1 x' r0' r1': ℝ>0),
  x' ≤ x ∧ r0' ≤ r0 ∧ r1 ≤ r1'
  →
  if x' < x ∨ r0' < r0 ∨ r1 < r1'
  then sx x r0 r1 < sx x' r0' r1'
  else sx x r0 r1 ≤ sx x' r0' r1'

def SX.homogeneous (sx: SX): Prop :=
∀ (a x r0 r1: ℝ>0), sx (a*x) (a*r0) (a*r1) = sx x r0 r1
