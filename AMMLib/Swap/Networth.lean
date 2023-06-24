import AMMLib.Swap.Basic
import AMMLib.Networth
import AMMLib.Swap.Rate

@[simp] theorem swap_price_mint_diff
(sw: Swap sx o s a t0 t1 v0)
(t0' t1': 𝕋₀) (hdif: m ≠ sw.exi.mint)
: sw.apply.𝕋₁Pricez' o t0' t1' = s.𝕋₁Pricez' o t0' t1' := by
  simp [Γ.𝕋₁Pricez']
  simp [Γ.𝕋₁Price_numz, Γ.𝕋₁Price_denumz, 
        Γ.𝕋₁Price_num_addend1z, Γ.𝕋₁Price_num_addend2z]
  simp [hdif]

/-
I must prove
𝕎₁.networth (Finsupp.erase (𝕋₀.toMint (_ : sw.t0 ≠ sw.t1)) (sw.apply.mints sw.a)) (Swap.apply sw) c.o

is equal to

𝕎₁.networth (Finsupp.erase (𝕋₀.toMint (_ : sw.t0 ≠ sw.t1)) (s sw.a)) (Swap.apply sw) c.o
-/

theorem bruh
(sw: Swap sx o s a t0 t1 v0) (a': 𝔸):
∀ (m: 𝕋₁), m ∈ (Finsupp.erase sw.exi.mint (sw.apply.mints a')).support → (mintedworth sw.apply o) m ((Finsupp.erase sw.exi.mint (sw.apply.mints a')) m) = (mintedworth s o) m ((Finsupp.erase sw.exi.mint (sw.apply.mints a')) m)
:= by
  intro m hin
  simp at hin
  have hdif := hin.1
  simp [mintedworth, hdif]
  left

@[simp] theorem networth_erase
(sw: Swap sx o s a t0 t1 v0) (a': 𝔸):
𝕎₁.networth (Finsupp.erase sw.mint (sw.apply.mints a')) sw.apply o
=
𝕎₁.networth (Finsupp.erase sw.mint (s.mints a')) s o
:= by
  simp [𝕎₁.networth]
  rw [@Finsupp.sum_congr 𝕋₁ NNReal NNReal _ _ _ (mintedworth (sw.apply) o) (mintedworth s o) (bruh sw a')]
  simp [Swap.apply]

theorem lemma32_same'
(sw: Swap sx o s a t0 t1 v0)
: 
(a.gain o s sw.apply)
=
v0*((sx v0 (s.amms.r0 t0 t1 sw.exi) (s.amms.r1 t0 t1 sw.exi))*(o t1) - (o t0))*(1 - (s.mints a sw.exi.mint)/(s.mints.supply sw.exi.mint))
:= by 
  unfold 𝔸.gain
  unfold Γ.networth

  rw [𝕎₀.networth_destruct _ o t0]
  rw [𝕎₀.networth_destruct _ o t1]
  rw [𝕎₀.networth_destruct (s.atoms a) o t0]
  rw [𝕎₀.networth_destruct (Finsupp.erase t0 (s.atoms a)) o t1]

  rw [Finsupp.erase_ne sw.exi.dif.symm]
  rw [Finsupp.erase_ne sw.exi.dif.symm]

  rw [𝕎₁.networth_destruct _ (sw.apply) o sw.exi.mint]
  rw [𝕎₁.networth_destruct _ s o sw.exi.mint]

  /-
  sx : SX
  o : 𝕆
  s : Γ
  a : 𝔸
  t0 t1 : 𝕋₀
  v0 : ℝ+
  sw : Swap sx o s a t0 t1 v0
  ⊢ ↑(o t0) * ↑(↑(↑s.atoms a) t0 - ↑v0) +
          (↑(o t1) * (↑(Swap.y sw) + ↑(↑(↑s.atoms a) t1)) +
            ↑(𝕎₀.networth (Finsupp.erase t1 (Finsupp.erase t0 (↑(Swap.apply sw).atoms a))) o)) +
        (↑(Γ.𝕋₁Pricez (Swap.apply sw) o (𝕊ₐ.init.mint (_ : 𝕊ₐ.init s.amms t0 t1))) *
            ↑(↑(↑(Swap.apply sw).mints a) (𝕊ₐ.init.mint (_ : 𝕊ₐ.init s.amms t0 t1))) +
          ↑(𝕎₁.networth (Finsupp.erase (𝕊ₐ.init.mint (_ : 𝕊ₐ.init s.amms t0 t1)) (↑(Swap.apply sw).mints a))
              (Swap.apply sw) o)) -
      (↑(o t0) * ↑(↑(↑s.atoms a) t0) +
          (↑(o t1) * ↑(↑(↑s.atoms a) t1) + ↑(𝕎₀.networth (Finsupp.erase t1 (Finsupp.erase t0 (↑s.atoms a))) o)) +
        (↑(Γ.𝕋₁Pricez s o (𝕊ₐ.init.mint (_ : 𝕊ₐ.init s.amms t0 t1))) *
            ↑(↑(↑s.mints a) (𝕊ₐ.init.mint (_ : 𝕊ₐ.init s.amms t0 t1))) +
          ↑(𝕎₁.networth (Finsupp.erase (𝕊ₐ.init.mint (_ : 𝕊ₐ.init s.amms t0 t1)) (↑s.mints a)) s o))) =
    ↑v0 *
        (↑(sx v0 (𝕊ₐ.r0 s.amms t0 t1 (_ : 𝕊ₐ.init s.amms t0 t1)) (𝕊ₐ.r1 s.amms t0 t1 (_ : 𝕊ₐ.init s.amms t0 t1))) *
            ↑(o t1) -
          ↑(o t0)) *
      (1 -
        ↑(↑(↑s.mints a) (𝕊ₐ.init.mint (_ : 𝕊ₐ.init s.amms t0 t1))) /
          ↑(𝕊₁.supply s.mints (𝕊ₐ.init.mint (_ : 𝕊ₐ.init s.amms t0 t1))))
  -/

  /-
  sx : SX
  o : 𝕆
  s : Γ
  a : 𝔸
  t0 t1 : 𝕋₀
  v0 : ℝ+
  sw : Swap sx o s a t0 t1 v0
  ⊢ ↑(↑(o t0) * (↑(↑s.atoms a) t0 - ↑v0) +
            (↑(o t1) * (↑(Swap.y sw) + ↑(↑s.atoms a) t1) +
              𝕎₀.networth (Finsupp.erase t1 (Finsupp.erase t0 (↑(Swap.apply sw).atoms a))) o) +
          (Γ.𝕋₁Pricez (Swap.apply sw) o (𝕊ₐ.init.mint (_ : 𝕊ₐ.init s.amms t0 t1)) *
              ↑(↑(Swap.apply sw).mints a) (𝕊ₐ.init.mint (_ : 𝕊ₐ.init s.amms t0 t1)) +
            𝕎₁.networth (Finsupp.erase (𝕊ₐ.init.mint (_ : 𝕊ₐ.init s.amms t0 t1)) (↑(Swap.apply sw).mints a))
              (Swap.apply sw) o)) -
      ↑(↑(o t0) * ↑(↑s.atoms a) t0 +
            (↑(o t1) * ↑(↑s.atoms a) t1 + 𝕎₀.networth (Finsupp.erase t1 (Finsupp.erase t0 (↑s.atoms a))) o) +
          (Γ.𝕋₁Pricez s o (𝕊ₐ.init.mint (_ : 𝕊ₐ.init s.amms t0 t1)) *
              ↑(↑s.mints a) (𝕊ₐ.init.mint (_ : 𝕊ₐ.init s.amms t0 t1)) +
            𝕎₁.networth (Finsupp.erase (𝕊ₐ.init.mint (_ : 𝕊ₐ.init s.amms t0 t1)) (↑s.mints a)) s o)) =
    ↑v0 *
        (↑(sx v0 (𝕊ₐ.r0 s.amms t0 t1 (_ : 𝕊ₐ.init s.amms t0 t1)) (𝕊ₐ.r1 s.amms t0 t1 (_ : 𝕊ₐ.init s.amms t0 t1))) *
            ↑(o t1) -
          ↑(o t0)) *
      (1 -
        ↑(↑(↑s.mints a) (𝕊ₐ.init.mint (_ : 𝕊ₐ.init s.amms t0 t1))) /
          ↑(𝕊₁.supply s.mints (𝕊ₐ.init.mint (_ : 𝕊ₐ.init s.amms t0 t1))))
  -/
  rw [Swap.b0_self, Swap.b1_self]
  unfold Swap.y
  simp
  sorry

@[simp] theorem swap_price_mint_denumz
(sw: Swap sx o s a t0 t1 v0)
(m: 𝕋₁)
: sw.apply.𝕋₁Price_denumz m = s.𝕋₁Price_denumz m := by
  simp [Γ.𝕋₁Price_denumz, Swap.apply, Γ.mintsupply]

@[simp] theorem Swap.mintsupply 
  (sw: Swap sx o s a t0 t1 v0) (m: 𝕋₁):
  sw.apply.mintsupply m = s.mintsupply m := by sorry

@[simp] theorem swap_price_mint'
(sw: Swap sx o s a t0 t1 v0)
(m: 𝕋₁)
: sw.apply.𝕋₁Pricez' o t0 t1 (by simp[sw.exi]) = s.𝕋₁Pricez' o t0 t1 sw.exi := by
  /-
  sx : SX
  o : 𝕆
  s : Γ
  a : 𝔸
  t0 t1 : 𝕋₀
  v0 : ℝ+
  sw : Swap sx o s a t0 t1 v0
  m : 𝕋₁
  ⊢ (↑(v0 + 𝕊ₐ.r0 s.amms t0 t1 (_ : 𝕊ₐ.init s.amms t0 t1)) * ↑(o t0) +
        ↑(PReal.sub (𝕊ₐ.r1 s.amms t0 t1 (_ : 𝕊ₐ.init s.amms t0 t1))
              (v0 * sx v0 (𝕊ₐ.r0 s.amms t0 t1 (_ : 𝕊ₐ.init s.amms t0 t1)) (𝕊ₐ.r1 s.amms t0 t1 (_ : 𝕊ₐ.init s.amms t0 t1)))
              (_ :
                v0 *
                    sx v0 (𝕊ₐ.r0 s.amms t0 t1 (_ : 𝕊ₐ.init s.amms t0 t1))
                      (𝕊ₐ.r1 s.amms t0 t1 (_ : 𝕊ₐ.init s.amms t0 t1)) <
                  𝕊ₐ.r1 s.amms t0 t1 (_ : 𝕊ₐ.init s.amms t0 t1))) *
          ↑(o t1)) /
      Γ.mintsupply s (𝕊ₐ.init.mint (_ : 𝕊ₐ.init (Swap.apply sw).amms t0 t1)) =
    (↑(𝕊ₐ.r0 s.amms t0 t1 (_ : 𝕊ₐ.init s.amms t0 t1)) * ↑(o t0) +
        ↑(𝕊ₐ.r1 s.amms t0 t1 (_ : 𝕊ₐ.init s.amms t0 t1)) * ↑(o t1)) /
      Γ.mintsupply s (𝕊ₐ.init.mint (_ : 𝕊ₐ.init s.amms t0 t1))
  -/
  simp [Γ.𝕋₁Pricez', Swap.y, PReal.coe_sub', PReal.coe_mul']

@[simp] theorem swap_price_mint_diff_num_addend1z
(sw: Swap sx o s a t0 t1 v0)
(m: 𝕋₁) (hdif: m ≠ sw.mint)
: sw.apply.𝕋₁Price_num_addend1z o m = s.𝕋₁Price_num_addend1z o m := by
  simp only [Γ.𝕋₁Price_num_addend1z]; left
  simp [Swap.apply, hdif]
  rw [← 𝕋₁.choose_eq m] at hdif
  unfold Swap.mint at hdif
  have hdif' := 𝕋₀.toMint_diff hdif
  simp [𝕊ₐ.sub_r1, hdif']
  simp [𝕊ₐ.add_r0, hdif']

@[simp] theorem swap_price_mint_diff_num_addend2z
(sw: Swap sx o s a t0 t1 v0)
(m: 𝕋₁) (hdif: m ≠ sw.mint)
: sw.apply.𝕋₁Price_num_addend2z o m = s.𝕋₁Price_num_addend2z o m := by
  simp [Γ.𝕋₁Price_num_addend2z]; left;
  simp [Swap.apply, hdif]
  rw [← 𝕋₁.choose_eq m] at hdif
  unfold Swap.mint at hdif
  have hdif' := 𝕋₀.toMint_diff hdif
  simp [𝕊ₐ.sub_r1, hdif']
  simp [𝕊ₐ.add_r0, hdif']

@[simp] theorem swap_price_mint_diff_numz
(sw: Swap sx o s a t0 t1 v0)
(m: 𝕋₁) (hdif: m ≠ sw.mint)
: sw.apply.𝕋₁Price_numz o m = s.𝕋₁Price_numz o m := by
simp [Γ.𝕋₁Price_numz]
simp [hdif]

@[simp] theorem Swap.apply_mints
(sw: Swap sx o s a t0 t1 v0):
sw.apply.mints = s.mints := by
simp [apply]

@[simp] theorem networth_erase'
(sw: Swap sx o s a t0 t1 v0) (a': 𝔸):
𝕎₁.networth (Finsupp.erase sw.mint (s.mints a')) sw.apply o
=
𝕎₁.networth (Finsupp.erase sw.mint (s.mints a')) s o
:= by
  have h := networth_erase sw a'
  simp only [Swap.apply_mints] at h
  exact h

theorem lemma32_same
(sw: Swap sx o s a t0 t1 v0)
: 
(a.gain ⟨sx,o⟩ s sw.apply)
=
v0*((sx v0 (s.amms.fp sw.exi).fst (s.amms.fp sw.exi).snd)*(o t1) - (o t0))*(1 - (s.mints a sw.mint)/(s.mints.supply sw.mint))
:= by
  unfold 𝔸.gain
  unfold Γ.networth
  rw [𝕎₀.networth_destruct _ o t0]
  rw [𝕎₀.networth_destruct _ o t1]
  rw [𝕎₀.networth_destruct (s.atoms a) o t0]
  rw [𝕎₀.networth_destruct (Finsupp.erase t0 (s.atoms a)) o t1]
  simp only [Swap.acc_t0_after_swap]
  rw [Finsupp.erase_ne sw.hdif.symm]
  rw [Finsupp.erase_ne sw.hdif.symm]
  simp only [Swap.acc_t1_after_swap]
  rw [𝕎₁.networth_destruct _ (sw.apply) o sw.mint]
  rw [𝕎₁.networth_destruct _ s o sw.mint]
  simp [Γ.𝕋₁Pricez, Γ.𝕋₁Price_numz, Γ.𝕋₁Price_denumz, Γ.𝕋₁Price_num_addend1z, Γ.𝕋₁Price_num_addend2z]

  unfold Swap.mint
  cases (𝕋₀.toMint_t0_cases sw.hdif) 
  with
  | inl chooseEq
  | inr chooseEq =>
      simp [chooseEq]
      simp [Γ.mintsupply, sw.enough, 
            le_of_lt sw.nodrain',
            𝕊ₐ.reorder_fst _ t1 t0,
            𝕊ₐ.reorder_snd _ t1 t0]
      field_simp
      ring_nf

theorem lemma32_diff
(sw: Swap sx o s a t0 t1 v0)
(a': 𝔸) (adif: a' ≠ a)
: 
(a'.gain ⟨sx,o⟩ s sw.apply)
=
-v0*((sx v0 (s.amms.fp sw.exi).fst (s.amms.fp sw.exi).snd)*(o t1) - (o t0))*((s.mints a' sw.mint)/(s.mints.supply sw.mint))
:= by
  unfold 𝔸.gain
  unfold Γ.networth
  rw [𝕎₀.networth_destruct _ o t0]
  rw [𝕎₀.networth_destruct _ o t1]
  rw [𝕎₀.networth_destruct (s.atoms a') o t0]
  rw [𝕎₀.networth_destruct (Finsupp.erase t0 (s.atoms a')) o t1]
  rw [Finsupp.erase_ne sw.hdif.symm]
  rw [Finsupp.erase_ne sw.hdif.symm]
  simp only [Swap.acc_diff_t1]
  rw [𝕎₁.networth_destruct _ (sw.apply) o sw.mint]
  rw [𝕎₁.networth_destruct _ s o sw.mint]
  simp [Γ.𝕋₁Pricez, Γ.𝕋₁Price_numz, Γ.𝕋₁Price_denumz, Γ.𝕋₁Price_num_addend1z, Γ.𝕋₁Price_num_addend2z]
  rw [Swap.acc_diff_t0 sw a' adif]

  unfold Swap.mint
  cases (𝕋₀.toMint_t0_cases sw.hdif) 
  with
  | inl chooseEq
  | inr chooseEq =>
      simp [chooseEq]
      simp [Γ.mintsupply, sw.enough, 
            le_of_lt sw.nodrain',
            𝕊ₐ.reorder_fst _ t1 t0,
            𝕊ₐ.reorder_snd _ t1 t0]
      field_simp
      ring_nf

theorem lemma33
(sw: Swap sx o s a t0 t1 v0)
(hzero: s.mints a sw.mint = 0):
cmp (a.gain ⟨sx,o⟩ s sw.apply) 0
=
cmp ((sx v0 (s.amms.fp sw.exi).fst (s.amms.fp sw.exi).snd)) ((o t0) / (o t1))
:= by 
  simp [lemma32_same, hzero, PReal.coe_div]

  generalize sx v0 (s.amms.fp sw.exi).fst (s.amms.fp sw.exi).snd = y at *
  generalize (o t0) = p0 at *
  generalize (o t1) = p1 at *
  generalize v0 = x at *

  conv => lhs; congr; rfl; rw [← (mul_zero (x: ℝ))]
  rw [cmp_mul_pos_left x.coe_pos (y*p1 - p0) 0]
  rw [← cmp_add_right ((y: ℝ)*p1 - p0) 0 p0]
  rw [zero_add, sub_add, sub_self, sub_zero]
  rw [div_eq_mul_inv p0 p1]
  rw [← cmp_mul_pos_right (inv_pos_of_pos p1.coe_pos) (y*p1) p0]
  rw [mul_inv_cancel_right₀ p1.coe_ne_zero y]
  rw [← PReal.coe_inv, ← PReal.coe_mul]
  exact PReal.coe_cmp y (p0*p1⁻¹)

theorem lemma33_lt
(sw: Swap sx o s a t0 t1 v0)
(hzero: s.mints a sw.mint = 0):
(a.gain ⟨sx,o⟩ s sw.apply) < 0
↔
((sx v0 (s.amms.fp sw.exi).fst (s.amms.fp sw.exi).snd)) <  (o t0) / (o t1)
:= by 
  rw [← cmp_eq_lt_iff, ← cmp_eq_lt_iff]
  rw [lemma33 sw hzero]

theorem lemma33_gt
(sw: Swap sx o s a t0 t1 v0)
(hzero: s.mints a sw.mint = 0):
0 < (a.gain ⟨sx,o⟩ s sw.apply)
↔
(o t0) / (o t1) < ((sx v0 (s.amms.fp sw.exi).fst (s.amms.fp sw.exi).snd))
:= by 
  rw [← cmp_eq_gt_iff, ← cmp_eq_gt_iff]
  rw [lemma33 sw hzero]

def Swap.swappedtoks
(sw: Swap sx o s a t0 t1 v0)
{x: ℝ+} (henough: x ≤ s.atoms a t1)
(nodrain: x*(sx x (s.amms.fp sw.exi_swap).fst (s.amms.fp sw.exi_swap).snd) < (s.amms.f t1 t0).snd): Swap sx o s a t1 t0 x := 
⟨
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
(sw: Swap SX.constprod o s a t0 t1 v0)
(hzero: s.mints a sw.mint = 0)
(y: ℝ+) (hy: y ≤ s.atoms a t1)
(nodrain: y*(SX.constprod y (s.amms.fp sw.exi_swap).fst (s.amms.fp sw.exi_swap).snd) < (s.amms.f t1 t0).snd)
(hgain: 0 < a.gain ⟨sx,o⟩ s sw.apply):
a.gain ⟨sx,o⟩ s (sw.swappedtoks hy nodrain).apply < 0 :=
  by
  have hmin: sw.mint = (sw.swappedtoks hy nodrain).mint := 
    by simp [swappedtoks, mint, 𝕋₀.toMint]

  have h1' := (lemma33_gt sw hzero).mp hgain

  apply (lemma33_lt (sw.swappedtoks hy nodrain) (by rw [hmin] at hzero; exact hzero)).mpr

  apply SX.lemma61_constprod v0
  simp only [swappedtoks]
  rw [𝕊ₐ.reorder_fstp s.amms t1 t0,
      𝕊ₐ.reorder_sndp s.amms t1 t0]
  exact le_of_lt h1'


