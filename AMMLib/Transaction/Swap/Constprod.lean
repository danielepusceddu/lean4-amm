import AMMLib.Transaction.Swap.Rate
import AMMLib.Transaction.Swap.Additive
import AMMLib.Transaction.Swap.Reversible
import HelpersLib.PReal.Sqrt
import HelpersLib.PReal.Order

noncomputable def SX.constprod: SX :=
  λ (x r0 r1: ℝ>0) => r1/(r0 + x)

def SX.constprod.outputbound: SX.outputbound SX.constprod := by
  unfold SX.outputbound
  intro x r0 r1
  unfold constprod
  rw [div_eq_mul_inv, ← mul_assoc, mul_inv_lt_iff_lt_mul]
  rw [left_distrib, mul_comm x r1]
  exact PReal.lt_add_left _ _

def SX.constprod.reversible:
  SX.reversible SX.constprod SX.constprod.outputbound := by
  unfold SX.reversible constprod
  intro x r0 r1
  rw [PReal.sub_y_add_y]
  rw [one_div, inv_div, add_comm]

theorem SX.constprod.homogeneous:
  homogeneous constprod := by
  unfold homogeneous
  intro a x r0 r1
  unfold constprod
  rw [← left_distrib, div_eq_mul_inv, inv_mul']
  rw [div_eq_mul_inv, mul_assoc, ← mul_assoc r1 _]
  rw [mul_comm r1, ← mul_assoc, ← mul_assoc a]
  simp [div_eq_mul_inv]

theorem SX.constprod.strictmono:
  strictmono constprod := by
  unfold strictmono
  intro x r0 r1 x' r0' r1'
  intro ⟨a,b,c⟩
  unfold constprod
  have h': r0'+x' ≤ r0+x := add_le_add b a
  if h: x' < x ∨ r0' < r0 ∨ r1 < r1'
  then
    simp only [h, ite_true]
    rw [div_lt_div_iff']
    rcases c.lt_or_eq with c'|c'
    <;> (
    rcases h with a|b|c
    . have h': r0'+x' < r0+x := add_lt_add_of_le_of_lt b a
      simp [Right.mul_lt_mul, c', h']
    . have h': r0'+x' < r0+x := add_lt_add_of_lt_of_le b a
      simp [Right.mul_lt_mul, c', h']
    . rcases h'.lt_or_eq with h'|h'
      <;> simp [c, h', Right.mul_lt_mul]
    )
  else
    simp only [h, div_le_iff_le_mul, ite_false, ge_iff_le]
    refine mul_inv_le_iff_le_mul.mp ?_
    rw [← div_eq_mul_inv, div_le_div_iff']
    exact mul_le_mul' c h'

theorem SX.constprod.additive: SX.additive SX.constprod := by
  unfold additive
  intro x y r0 r1 h
  have desimp: y*r1 = (y*r0*r1 + y*x*r1)/(r0+x) := by
    symm
    rw [mul_comm y x, mul_comm y r0]
    rw [mul_assoc, mul_assoc]
    rw [← right_distrib]
    rw [mul_comm, div_eq_mul_inv, mul_assoc]
    simp
  simp_rw [constprod]
  rw [div_eq_div_iff_mul_eq_mul]
  rw [right_distrib]
  simp_rw [mul_div]
  rw [PReal.mul_sub']
  simp_rw [mul_div, desimp]
  rw [PReal.div_sub_div_same' _ _ _ (by simp [mul_assoc])]
  simp_rw [← mul_assoc]
  rw [PReal.add_sub]
  simp_rw [div_mul]
  rw [div_right_comm]
  rw [div_div]
  simp_rw [div_eq_mul_inv]
  rw [mul_inv _ (r0 + x)]
  rw [mul_inv (r0 + x + y)]
  rw [mul_assoc _ _ ((r0+x)⁻¹)]
  rw [← mul_inv]
  rw [mul_comm _ (r0+x)]
  rw [← mul_assoc]
  rw [← right_distrib]
  rw [eq_mul_inv_iff_mul_eq]
  rw [← mul_assoc]
  rw [mul_inv_eq_iff_eq_mul]
  rw [right_distrib]
  rw [mul_assoc (y*r0*r1) _ (r0 + (x + y))]
  rw [add_assoc]
  rw [mul_left_inv, mul_one]
  rw [left_distrib, left_distrib, right_distrib, right_distrib,
      left_distrib, left_distrib]
  rw [← add_assoc, ← add_assoc]
  rw [mul_comm r1 x]
  rw [add_assoc _ _ (x*r1*x), add_comm _ ((x*r1*x))]
  rw [mul_rotate x r1 r0]
  rw [←add_assoc]
  rw [← add_rotate _ _ (r1*y*r0)]
  rw [mul_rotate y r0 r1, mul_rotate r0 r1 y]
  rw [add_left_inj]
  rw [add_comm (r1*y*x) _, add_right_inj]
  rw [← mul_rotate]


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
theorem SX.constprod.exchrate_vs_oracle
  (x r0 r1 p0 p1: ℝ>0)
  (h: p0/p1 ≤ constprod x r0 r1):
  ∀ (y: ℝ>0), constprod y r1 r0 < p1/p0 := by
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


/-
Unique direction for swap gains Sketch Proof
With sw1,sw2,sx1,sx2 for original and swapped

h0: We know mintedb = 0
h1: We know gain sw1 > 0
            0 < gain sw1
            sx1 > p0/p1    by lemma 3.3 with h0

Goal:
  gain sw2 < 0
  sx2 < p1/p0   by lemma 3.3 with h0
  p0/p1 ≤ sx x r0 r1 by applying lemma 6.1
  Qed by h1
-/
theorem SX.constprod.gain_direction
  (sw1: Swap SX.constprod s a t0 t1 x)
  (sw2: Swap SX.constprod s a t1 t0 x') (o: O)
  (hzero: (s.mints.get a).get t0 t1 = 0)
  (hgain: 0 < a.gain o s sw1.apply):
  a.gain o s sw2.apply < 0 :=
  by
  have hzero': (s.mints.get a).get t1 t0 = 0 :=
               by rw [W₁.get_reorder _ t1 t0]; exact hzero

  -- First modus ponens
  -- ammrate(t1,t0) < extrate(t1,t0) → sw2gain < 0
  apply (Swap.swaprate_vs_exchrate_lt sw2 o hzero').mpr

  -- Second modus ponens
  -- extrate(t0,t1) ≤ ammrate(t0,t1)
  -- →
  -- ammrate(t1,t0) < extrate(t1,t0)
  apply exchrate_vs_oracle x
  rw [AMMs.r0_reorder s.amms t1 t0,
      AMMs.r1_reorder s.amms t1 t0]
  exact le_of_lt
        ((Swap.swaprate_vs_exchrate_gt sw1 o hzero).mp hgain)

theorem SX.constprod.optimality_suff
  (sw1: Swap SX.constprod s a t0 t1 x₀)
  (o: O)
  (h: sw1.apply.amms.r1 t0 t1 (by simp[sw1.exi]) / sw1.apply.amms.r0 t0 t1 (by simp[sw1.exi]) = (o t0) / (o t1)):
  sw1.is_solution o := by
  unfold Swap.is_solution
  intro x sw2 hdif hzero

  have addi: SX.additive SX.constprod := SX.constprod.additive
  have bound: SX.outputbound SX.constprod := SX.constprod.outputbound
  have rev: SX.reversible SX.constprod bound := SX.constprod.reversible

  rcases Decidable.em (x₀ < x) with le|nle
  . have ⟨x₁, prop₁⟩ := PReal.lt_iff_exists_add le
    have sw2' := sw2
    rw [prop₁] at sw2'
    rw [Swap.apply_same_val sw2 sw2' prop₁]

    have sw3: Swap SX.constprod sw1.apply a t0 t1 x₁ :=
      sw2'.bound_split2 bound

    rw [Swap.additive_gain sw1 sw3 sw2' addi o]

    have sw3_rate_lt_exch: sw3.rate < o t0 / o t1 := by
      simp [Swap.rate, SX.constprod, ← h]
    simp [(Swap.swaprate_vs_exchrate_lt sw3 o hzero).mpr sw3_rate_lt_exch]

  . have le: x ≤ x₀ := not_lt.mp nle
    have lt: x < x₀ := hdif.symm.lt_of_le' le
    have ⟨x₁, prop₁⟩ := PReal.lt_iff_exists_add lt
    have sw1' := sw1
    rw [prop₁] at sw1'
    rw [Swap.apply_same_val sw1 sw1' prop₁]
    have sw3: Swap SX.constprod sw2.apply a t0 t1 x₁ :=
      sw1'.bound_split2 bound
    rw [Swap.additive_gain sw2 sw3 sw1' addi o]
    rw [← Swap.rev_gain sw3 rev o]

    have sw3_invrate_lt: (sw3.inv rev).rate < o t1 / o t0 := by
      rw [Swap.rate_of_inv_eq_inv_rate]
      rw [inv_lt', inv_div]
      rw [← h]
      unfold Swap.rate
      unfold SX.constprod
      simp only [Swap.amms, AMMs.r1_of_add_r0, AMMs.r1_of_sub_r1,
                 AMMs.r0_of_add_r0, AMMs.r0_of_sub_r1,
                 Swap.y, prop₁, Swap.rate]

      -- same denumerator
      rw [add_assoc, add_comm x₁ _, ← add_assoc x _ _]
      rw [div_lt_div_iff_right]

      -- remove r1
      rw [PReal.x_sub_y_lt_x_sub_z_iff]

      rw [mul_div, mul_div]
      rw [div_lt_div_iff']

      -- distributivity
      simp_rw [right_distrib]
      simp_rw [left_distrib]
      rw [add_assoc]
      rw [add_lt_add_iff_left]
      rw [add_lt_add_iff_left]
      rw [add_comm]
      rw [mul_comm _ x₁, mul_comm x _, ← mul_assoc]
      exact PReal.lt_add_right _ _

    have hzero': (sw3.apply.mints.get a).get t1 t0 = 0 := by
      simp [hzero, W₁.get_reorder _ t1 t0]

    have sw3_inv_gain_neg :=
      (Swap.swaprate_vs_exchrate_lt (sw3.inv rev) o hzero').mpr sw3_invrate_lt

    exact lt_add_of_pos_right _ (neg_pos.mpr sw3_inv_gain_neg)

/-
(r1 - ((PReal.sqrt(p1 * p0⁻¹ * r0 * r1) - r0) * (r1 / PReal.sqrt (p1 * p0⁻¹ * r0 * r1))))
/
PReal.sqrt(p1 * p0⁻¹ * r0 * r1)


= RIGHT DISTRIB

(r1 - ((PReal.sqrt (p1 * p0⁻¹ * r0 * r1) * r1 / PReal.sqrt (p1 * p0⁻¹ * r0 * r1) - r0 * r1 / PReal.sqrt (p1 * p0⁻¹ * r0 * r1))))
/
PReal.sqrt(p1 * p0⁻¹ * r0 * r1)

= SIMP X/X

(r1 - ((r1 - r0 * r1 / PReal.sqrt (p1 * p0⁻¹ * r0 * r1))))
/
PReal.sqrt(p1 * p0⁻¹ * r0 * r1)

= SUB SUB ''

(r1+r0 * r1 / PReal.sqrt (p1 * p0⁻¹ * r0 * r1) - r1)
/
PReal.sqrt(p1 * p0⁻¹ * r0 * r1)

= ADD COMM

(r0 * r1 / PReal.sqrt (p1 * p0⁻¹ * r0 * r1) + r1 - r1)
/
PReal.sqrt(p1 * p0⁻¹ * r0 * r1)

= ADD Y SUB Y

(r0 * r1 / PReal.sqrt (p1 * p0⁻¹ * r0 * r1))
/
PReal.sqrt(p1 * p0⁻¹ * r0 * r1)

= div div

(r0 * r1 / (PReal.sqrt (p1 * p0⁻¹ * r0 * r1) * PReal.sqrt (p1 * p0⁻¹ * r0 * r1)))

= sqrt * sqrt

(r0 * r1 / (p1 * p0⁻¹ * r0 * r1))

= simp

1 / (p1*p0⁻¹)

= inv of mul

p0*p1⁻¹

=

p0 / p1 GOAL
-/
theorem SX.constprod.arbitrage_solve
  (sw: Swap SX.constprod s a t0 t1 x₀)
  (o: O)
  (less: s.amms.r0 t0 t1 (by simp[sw.exi]) < ((o t1)*(o t0)⁻¹*(s.amms.r0 t0 t1 (by simp[sw.exi]))*(s.amms.r1 t0 t1 (by simp[sw.exi]))).sqrt)
  (h: x₀ = ((o t1)*(o t0)⁻¹*(s.amms.r0 t0 t1 (by simp[sw.exi]))*(s.amms.r1 t0 t1 (by simp[sw.exi]))).sqrt.sub (s.amms.r0 t0 t1 (by simp[sw.exi])) less):
  sw.is_solution o := by

  have aligned: sw.apply.amms.r1 t0 t1 (by simp[sw.exi]) / sw.apply.amms.r0 t0 t1 (by simp[sw.exi]) = (o t0) / (o t1) := by
    simp [Swap.y, Swap.rate, constprod, h]
    simp_rw [PReal.sub_mul'] -- right distrib step
    simp_rw [div_eq_mul_inv]
    simp_rw [mul_comm (s.amms.r1 t0 t1 sw.exi) _, ← mul_assoc _ _ (s.amms.r1 t0 t1 sw.exi), mul_right_inv, one_mul] -- simp x/x
    simp_rw [PReal.sub_sub'', add_comm (s.amms.r1 t0 t1 sw.exi) _, PReal.sub_of_add]
    rw [mul_comm, ← mul_assoc, mul_comm (s.amms.r0 t0 t1 sw.exi) _, ←mul_assoc, ←mul_inv, PReal.mul_self_sqrt _]
    simp_rw [mul_inv]; rw [inv_inv]
    rw [mul_assoc, mul_assoc, mul_assoc, mul_comm _ (o t0)]
    simp

  exact optimality_suff sw o aligned
