import AMMLib.Swap.Basic
import AMMLib.Networth
import AMMLib.Swap.Rate

@[simp] theorem swap_price_mint_diff
(sw: Swap sx o s a t0 t1 v0)
(t0' t1': 𝕋₀) (init: s.amms.init t0' t1') 
(hdif: diffpair t0 t1 t0' t1')
: sw.apply.𝕋₁Price o t0' t1' = s.𝕋₁Price o t0' t1' := by
  unfold Γ.𝕋₁Price
  simp [init, hdif]


/-
```
price(m) = (r0*p0 + r1*p1)/supply
after swap, becomes
(r0*p0 + x*p0 + r1*p1 - y*p1)/supply
=
(r0*p0 + r1*p1)/supply + (x*p0 - y*p1)/supply
= oldprice + (x*p0 - y*p1)/supply

The price may decrease. However, does it keep being positive?
0 < (r0*p0 + x*p0 + r1*p1 - y*p1)/supply
0 < r0*p0 + x*p0 + r1*p1 - y*p1   by positivity of supply
0 < p0(r0 + x) + p1(r1 - y)
Yes, both addends are positive, by y < r1

When does the price increase?
oldprice < oldprice + (x*p0 - y*p1)/supply
0 < (x*p0 - y*p1)/supply
0 < (x*p0 - y*p1)
y*p1 < x*p0

When does the price stay the same?
y*p1 = x*p0

When does the price decrease?
y*p1 > x*p0
```
-/
@[simp] theorem swap_price_mint_self
(sw: Swap sx o s a t0 t1 v0)
: sw.apply.𝕋₁Price o t0 t1 = ⟨(s.𝕋₁Price o t0 t1) + (((v0*(o t0)): ℝ) - sw.y*(o t1)) / (s.mints.supply t0 t1), by sorry⟩ := by
  unfold Γ.𝕋₁Price
  simp [sw.exi, PReal.coe_sub']
  sorry

/-
I must prove
𝕎₁.networth (Finsupp.erase (𝕋₀.toMint (_ : sw.t0 ≠ sw.t1)) (sw.apply.mints sw.a)) (Swap.apply sw) c.o

is equal to

𝕎₁.networth (Finsupp.erase (𝕋₀.toMint (_ : sw.t0 ≠ sw.t1)) (s sw.a)) (Swap.apply sw) c.o
-/

@[simp] theorem networth_erase
(sw: Swap sx o s a t0 t1 v0):
((sw.apply.mints.get a).drain t0 t1 sw.exi.dif)
=
((s.mints.get a).drain t0 t1 sw.exi.dif)
:= by
  sorry

theorem minca (sw: Swap sx o s a t0 t1 v0):
  (((sw.apply.atoms.get a).drain t0).drain t1).worth o = (((s.atoms.get a).drain t0).drain t1).worth o := by
  rw [𝕎₀.drain_comm _ t1 t0]
  rw [𝕎₀.drain_comm _ t1 t0]
  unfold Swap.apply
  simp [sw.exi.dif]

@[simp] theorem bruh' 
  (sw: Swap sx o s a t0 t1 v0) (w: 𝕎₁)
  (h: w.f t0 t1 = 0):
  w.worth (sw.apply.𝕋₁Price o) = w.worth (s.𝕋₁Price o) := by 
  sorry

theorem lemma32_same'
(sw: Swap sx o s a t0 t1 v0)
: 
(a.gain o s sw.apply)
=
(sw.y*(o t1) - v0*(o t0))*(1 - ((s.mints.get a).get t0 t1)/(s.mints.supply t0 t1))
:= by 
  unfold 𝔸.gain
  unfold Γ.networth

  rw [𝕎₀.worth_destruct _ o t0]
  rw [𝕎₀.worth_destruct _ o t1]
  rw [𝕎₀.worth_destruct (s.atoms.get a) o t0]
  rw [𝕎₀.worth_destruct ((s.atoms.get a).drain t0) o t1]

  rw [minca]
  rw [𝕎₁.worth_destruct _ (sw.apply.𝕋₁Price o) t0 t1 _]
  rw [𝕎₁.worth_destruct _ (s.𝕋₁Price o) t0 t1 _]

  simp
  simp [sw.exi.dif, sw.exi.dif.symm, sw.enough, sw.nodrain]
  ring_nf
  exact sw.exi.dif

theorem lemma33
(sw: Swap sx o s a t0 t1 x)
(hzero: (s.mints.get a).get t0 t1 = 0):
cmp (a.gain o s sw.apply) 0
=
cmp sw.rate ((o t0) / (o t1))
:= by 
  simp [lemma32_same', hzero, PReal.coe_div, Swap.y]

  generalize (o t0) = p0 at *
  generalize (o t1) = p1 at *

  rw [PReal.coe_mul, mul_assoc]
  rw [cmp_mul_pos_left x.coe_pos (sw.rate*p1) p0]
  rw [div_eq_mul_inv p0 p1]
  rw [← cmp_mul_pos_right (inv_pos_of_pos p1.coe_pos) (sw.rate*p1) p0]
  rw [mul_inv_cancel_right₀ p1.coe_ne_zero sw.rate]
  exact PReal.coe_cmp sw.rate (p0*p1⁻¹)

theorem lemma33_lt
(sw: Swap sx o s a t0 t1 v0)
(hzero: (s.mints.get a).get t0 t1 = 0):
(a.gain o s sw.apply) < 0
↔
sw.rate <  (o t0) / (o t1)
:= by 
  rw [← cmp_eq_lt_iff, ← cmp_eq_lt_iff]
  rw [lemma33 sw hzero]

theorem lemma33_gt
(sw: Swap sx o s a t0 t1 v0)
(hzero: (s.mints.get a).get t0 t1 = 0):
0 < (a.gain o s sw.apply)
↔
(o t0) / (o t1) < sw.rate
:= by 
  rw [← cmp_eq_gt_iff, ← cmp_eq_gt_iff]
  rw [lemma33 sw hzero]

def Swap.swappedtoks
(sw: Swap sx o s a t0 t1 v0)
{x: ℝ+} (henough: x ≤ s.atoms.get a t1)
(nodrain: x*(sx x (s.amms.r0 t1 t0 sw.exi.swap) (s.amms.r1 t1 t0 sw.exi.swap)) < (s.amms.r1 t1 t0 sw.exi.swap)): Swap sx o s a t1 t0 x := 
⟨
  henough,
  sw.exi.swap,
  nodrain
⟩

/-
Lemma 6.2: Unique direction for swap gains

Sketch Proof
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
theorem Swap.lemma62_constprod
(sw1: Swap SX.constprod o s a t0 t1 x)
(sw2: Swap SX.constprod o s a t1 t0 x')
(hzero: (s.mints.get a).get t0 t1 = 0)
(hgain: 0 < a.gain o s sw1.apply):
a.gain o s sw2.apply < 0 :=
  by

  have h1' := (lemma33_gt sw1 hzero).mp hgain

  apply (lemma33_lt sw2 (by rw [𝕎₁.get_reorder _ t1 t0]; exact hzero)).mpr

  apply SX.lemma61_constprod x
  simp only [swappedtoks]
  rw [𝕊ₐ.r0_reorder s.amms t1 t0,
      𝕊ₐ.r1_reorder s.amms t1 t0]
  exact le_of_lt h1'
