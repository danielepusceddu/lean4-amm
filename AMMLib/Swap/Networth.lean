import AMMLib.Swap.Basic
import AMMLib.Networth

@[simp] theorem swap_price_mint_denumz
{c: Cfg} {s: Γ} (sw: Swap c s)
(m: 𝕋₁)
: sw.apply.𝕋₁Price_denumz m = s.𝕋₁Price_denumz m := by
simp [Γ.𝕋₁Price_denumz]

@[simp] theorem swap_price_mint_diff_num_addend1z
{c: Cfg} {s: Γ} (sw: Swap c s)
(m: 𝕋₁) (hdif: m ≠ sw.mint)
: sw.apply.𝕋₁Price_num_addend1z c.o m = s.𝕋₁Price_num_addend1z c.o m := by
  simp [Γ.𝕋₁Price_num_addend1z]; left
  simp [Swap.apply, hdif]
  rw [← 𝕋₁.choose_eq m] at hdif
  unfold Swap.mint at hdif
  have hdif' := 𝕋₀.toMint_diff hdif
  simp [𝕊ₐ.sub_r1, hdif']
  simp [𝕊ₐ.add_r0, hdif']

@[simp] theorem swap_price_mint_diff_num_addend2z
{c: Cfg} {s: Γ} (sw: Swap c s)
(m: 𝕋₁) (hdif: m ≠ sw.mint)
: sw.apply.𝕋₁Price_num_addend2z c.o m = s.𝕋₁Price_num_addend2z c.o m := by
  simp [Γ.𝕋₁Price_num_addend2z]; left;
  simp [Swap.apply, hdif]
  rw [← 𝕋₁.choose_eq m] at hdif
  unfold Swap.mint at hdif
  have hdif' := 𝕋₀.toMint_diff hdif
  simp [𝕊ₐ.sub_r1, hdif']
  simp [𝕊ₐ.add_r0, hdif']

@[simp] theorem swap_price_mint_diff_numz
{c: Cfg} {s: Γ} (sw: Swap c s)
(m: 𝕋₁) (hdif: m ≠ sw.mint)
: sw.apply.𝕋₁Price_numz c.o m = s.𝕋₁Price_numz c.o m := by
simp [Γ.𝕋₁Price_numz]
simp [hdif]

@[simp] theorem swap_price_mint_diff
{c: Cfg} {s: Γ} (sw: Swap c s)
(m: 𝕋₁) (hdif: m ≠ sw.mint)
: sw.apply.𝕋₁Pricez c.o m = s.𝕋₁Pricez c.o m := by
  simp [Γ.𝕋₁Pricez]
  simp [hdif]

/-
I must prove
𝕎₁.networth (Finsupp.erase (𝕋₀.toMint (_ : sw.t0 ≠ sw.t1)) (sw.apply.mints sw.a)) (Swap.apply sw) c.o

is equal to

𝕎₁.networth (Finsupp.erase (𝕋₀.toMint (_ : sw.t0 ≠ sw.t1)) (s sw.a)) (Swap.apply sw) c.o
-/

theorem bruh
{c: Cfg} {s: Γ} (sw: Swap c s) (a: 𝔸):
∀ (m: 𝕋₁), m ∈ (Finsupp.erase sw.mint (sw.apply.mints a)).support → (mintedworth sw.apply c.o) m ((Finsupp.erase sw.mint (sw.apply.mints a)) m) = (mintedworth s c.o) m ((Finsupp.erase sw.mint (sw.apply.mints a)) m)
:= by
  intro m hin
  simp at hin
  have hdif := hin.1
  simp [mintedworth, hdif]

@[simp] theorem networth_erase
{c: Cfg} {s: Γ} (sw: Swap c s) (a: 𝔸):
𝕎₁.networth (Finsupp.erase sw.mint (sw.apply.mints a)) sw.apply c.o
=
𝕎₁.networth (Finsupp.erase sw.mint (s.mints a)) s c.o
:= by
  simp [𝕎₁.networth]
  rw [@Finsupp.sum_congr 𝕋₁ NNReal NNReal _ _ _ (mintedworth (sw.apply) c.o) (mintedworth s c.o) (bruh sw a)]
  simp [Swap.apply]

@[simp] theorem Swap.apply_mints
{c: Cfg} {s: Γ} (sw: Swap c s):
sw.apply.mints = s.mints := by
simp [apply]

@[simp] theorem networth_erase'
{c: Cfg} {s: Γ} (sw: Swap c s) (a: 𝔸):
𝕎₁.networth (Finsupp.erase sw.mint (s.mints a)) sw.apply c.o
=
𝕎₁.networth (Finsupp.erase sw.mint (s.mints a)) s c.o
:= by
  have h := networth_erase sw a
  simp only [Swap.apply_mints] at h
  exact h

theorem lemma32_same
{c: Cfg} {s: Γ} (sw: Swap c s)
: 
(sw.a.gain c s sw.apply)
=
sw.v0*((c.sx sw.v0 (s.amms.fp sw.exi).fst (s.amms.fp sw.exi).snd)*(c.o sw.t1) - (c.o sw.t0))*(1 - (s.mints sw.a sw.mint)/(s.mints.supply sw.mint))
:= by
  unfold 𝔸.gain
  unfold Γ.networth
  rw [𝕎₀.networth_destruct _ c.o sw.t0]
  rw [𝕎₀.networth_destruct _ c.o sw.t1]
  rw [𝕎₀.networth_destruct (s.atoms sw.a) c.o sw.t0]
  rw [𝕎₀.networth_destruct (Finsupp.erase sw.t0 (s.atoms sw.a)) c.o sw.t1]
  simp only [Swap.acc_t0_after_swap]
  rw [Finsupp.erase_ne sw.hdif.symm]
  rw [Finsupp.erase_ne sw.hdif.symm]
  simp only [Swap.acc_t1_after_swap]
  rw [𝕎₁.networth_destruct _ (sw.apply) c.o sw.mint]
  rw [𝕎₁.networth_destruct _ s c.o sw.mint]
  simp [Γ.𝕋₁Pricez, Γ.𝕋₁Price_numz, Γ.𝕋₁Price_denumz, Γ.𝕋₁Price_num_addend1z, Γ.𝕋₁Price_num_addend2z]

  unfold Swap.mint
  cases (𝕋₀.toMint_t0_cases sw.hdif) 
  with
  | inl chooseEq
  | inr chooseEq =>
      simp [chooseEq]
      simp [Γ.mintsupply, sw.enough, le_of_lt sw.nodrain,
            𝕊ₐ.reorder_fst _ sw.t1 sw.t0,
            𝕊ₐ.reorder_snd _ sw.t1 sw.t0]
      field_simp
      ring_nf

theorem lemma32_diff
{c: Cfg} {s: Γ} (sw: Swap c s)
(a: 𝔸) (adif: a ≠ sw.a)
: 
(a.gain c s sw.apply)
=
-sw.v0*((c.sx sw.v0 (s.amms.fp sw.exi).fst (s.amms.fp sw.exi).snd)*(c.o sw.t1) - (c.o sw.t0))*((s.mints a sw.mint)/(s.mints.supply sw.mint))
:= by
  unfold 𝔸.gain
  unfold Γ.networth
  rw [𝕎₀.networth_destruct _ c.o sw.t0]
  rw [𝕎₀.networth_destruct _ c.o sw.t1]
  rw [𝕎₀.networth_destruct (s.atoms a) c.o sw.t0]
  rw [𝕎₀.networth_destruct (Finsupp.erase sw.t0 (s.atoms a)) c.o sw.t1]
  rw [Finsupp.erase_ne sw.hdif.symm]
  rw [Finsupp.erase_ne sw.hdif.symm]
  simp only [Swap.acc_diff_t1]
  rw [𝕎₁.networth_destruct _ (sw.apply) c.o sw.mint]
  rw [𝕎₁.networth_destruct _ s c.o sw.mint]
  simp [Γ.𝕋₁Pricez, Γ.𝕋₁Price_numz, Γ.𝕋₁Price_denumz, Γ.𝕋₁Price_num_addend1z, Γ.𝕋₁Price_num_addend2z]
  rw [Swap.acc_diff_t0 sw a adif]

  unfold Swap.mint
  cases (𝕋₀.toMint_t0_cases sw.hdif) 
  with
  | inl chooseEq
  | inr chooseEq =>
      simp [chooseEq]
      simp [Γ.mintsupply, sw.enough, le_of_lt sw.nodrain,
            𝕊ₐ.reorder_fst _ sw.t1 sw.t0,
            𝕊ₐ.reorder_snd _ sw.t1 sw.t0]
      field_simp
      ring_nf

theorem lemma33
{c: Cfg} {s: Γ} (sw: Swap c s)
(hzero: s.mints sw.a sw.mint = 0):
cmp (sw.a.gain c s sw.apply) 0
=
cmp ((c.sx sw.v0 (s.amms.fp sw.exi).fst (s.amms.fp sw.exi).snd)) ((c.o sw.t0) / (c.o sw.t1))
:= by 
  simp [lemma32_same, hzero, PReal.coe_div]

  generalize c.sx sw.v0 (s.amms.fp sw.exi).fst (s.amms.fp sw.exi).snd = y at *
  generalize (c.o sw.t0) = p0 at *
  generalize (c.o sw.t1) = p1 at *
  generalize sw.v0 = x at *

  rw [← (mul_zero (x: ℝ))]
  rw [cmp_mul_pos_left x.coe_pos (y*p1 - p0) 0]
  rw [← cmp_add_right ((y: ℝ)*p1 - p0) 0 p0]
  rw [zero_add, sub_add, sub_self, sub_zero]
  rw [div_eq_mul_inv p0 p1]
  rw [← cmp_mul_pos_right (inv_pos_of_pos p1.coe_pos) (y*p1) p0]
  rw [mul_inv_cancel_right₀ p1.coe_ne_zero y]
  rw [← PReal.coe_inv, ← PReal.coe_mul]
  exact PReal.coe_cmp y (p0*p1⁻¹)

theorem lemma33_lt
{c: Cfg} {s: Γ} (sw: Swap c s)
(hzero: s.mints sw.a sw.mint = 0):
(sw.a.gain c s sw.apply) < 0
↔
((c.sx sw.v0 (s.amms.fp sw.exi).fst (s.amms.fp sw.exi).snd)) <  (c.o sw.t0) / (c.o sw.t1)
:= by 
  rw [← cmp_eq_lt_iff, ← cmp_eq_lt_iff]
  rw [lemma33 sw hzero]

theorem lemma33_gt
{c: Cfg} {s: Γ} (sw: Swap c s)
(hzero: s.mints sw.a sw.mint = 0):
0 < (sw.a.gain c s sw.apply)
↔
(c.o sw.t0) / (c.o sw.t1) < ((c.sx sw.v0 (s.amms.fp sw.exi).fst (s.amms.fp sw.exi).snd))
:= by 
  rw [← cmp_eq_gt_iff, ← cmp_eq_gt_iff]
  rw [lemma33 sw hzero]

def Swap.swappedtoks
{c: Cfg} {s: Γ} (sw: Swap c s)
{x: ℝ+} (henough: x ≤ s.atoms sw.a sw.t1)
(nodrain: x*(c.sx x (s.amms.fp sw.exi_swap).fst (s.amms.fp sw.exi_swap).snd) < (s.amms.f sw.t1 sw.t0).snd): Swap c s := 
⟨
  sw.t1,
  sw.t0,
  sw.a,
  x,
  henough,
  𝕊ₐ.exists_swap sw.exi,
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
{c: Cfg} {s: Γ} (sw: Swap c s)
(cons: c.sx = SX.constprod)
(hzero: s.mints sw.a sw.mint = 0)
(y: ℝ+) (hy: y ≤ s.atoms sw.a sw.t1)
(nodrain: y*(c.sx y (s.amms.fp sw.exi_swap).fst (s.amms.fp sw.exi_swap).snd) < (s.amms.f sw.t1 sw.t0).snd)
(hgain: 0 < sw.a.gain c s sw.apply):
sw.a.gain c s (sw.swappedtoks hy nodrain).apply < 0 :=
  by
  have hswa: sw.a = (sw.swappedtoks hy nodrain).a := 
    by simp [swappedtoks]
  have hmin: sw.mint = (sw.swappedtoks hy nodrain).mint := 
    by simp [swappedtoks, mint, 𝕋₀.toMint]
  rw [hswa]

  have h1' := (lemma33_gt sw hzero).mp hgain

  simp_rw [lemma33_lt (sw.swappedtoks hy nodrain) (by rw [hmin, hswa] at hzero; exact hzero)]

  simp_rw [cons] at h1'
  simp_rw [cons]
  apply SX.lemma61_constprod sw.v0
  simp only [swappedtoks]
  rw [𝕊ₐ.reorder_fstp s.amms sw.t1 sw.t0,
      𝕊ₐ.reorder_sndp s.amms sw.t1 sw.t0]
  exact le_of_lt h1'

