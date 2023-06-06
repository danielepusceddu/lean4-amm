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
sw.v0*((c.sx sw.v0 (s.amms.fp sw.exi))*(c.o sw.t1) - (c.o sw.t0))*(1 - (s.mints sw.a sw.mint)/(s.mints.supply sw.mint))
:= by
  unfold 𝔸.gain
  unfold Γ.networth
  rw [𝕎₀.networth_destruct _ c.o sw.t0]
  rw [𝕎₀.networth_destruct _ c.o sw.t1]
  rw [𝕎₀.networth_destruct (s.atoms sw.a) c.o sw.t0]
  rw [𝕎₀.networth_destruct (Finsupp.erase sw.t0 (s.atoms sw.a)) c.o sw.t1]
  simp only [Swap.acc_t0_after_swap]
  rw [Finsupp.erase_ne (𝕊ₐ.exists_imp_dif sw.exi).symm]
  rw [Finsupp.erase_ne (𝕊ₐ.exists_imp_dif sw.exi).symm]
  simp only [Swap.acc_t1_after_swap]
  rw [𝕎₁.networth_destruct _ (sw.apply) c.o sw.mint]
  rw [𝕎₁.networth_destruct _ s c.o sw.mint]
  simp [Γ.𝕋₁Pricez, Γ.𝕋₁Price_numz, Γ.𝕋₁Price_denumz, Γ.𝕋₁Price_num_addend1z, Γ.𝕋₁Price_num_addend2z]

  unfold Swap.mint
  cases (𝕋₀.toMint_t0_cases (𝕊ₐ.exists_imp_dif sw.exi)) 
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
-sw.v0*((c.sx sw.v0 (s.amms.fp sw.exi))*(c.o sw.t1) - (c.o sw.t0))*((s.mints a sw.mint)/(s.mints.supply sw.mint))
:= by
  unfold 𝔸.gain
  unfold Γ.networth
  rw [𝕎₀.networth_destruct _ c.o sw.t0]
  rw [𝕎₀.networth_destruct _ c.o sw.t1]
  rw [𝕎₀.networth_destruct (s.atoms a) c.o sw.t0]
  rw [𝕎₀.networth_destruct (Finsupp.erase sw.t0 (s.atoms a)) c.o sw.t1]
  rw [Finsupp.erase_ne (𝕊ₐ.exists_imp_dif sw.exi).symm]
  rw [Finsupp.erase_ne (𝕊ₐ.exists_imp_dif sw.exi).symm]
  simp only [Swap.acc_diff_t1]
  rw [𝕎₁.networth_destruct _ (sw.apply) c.o sw.mint]
  rw [𝕎₁.networth_destruct _ s c.o sw.mint]
  simp [Γ.𝕋₁Pricez, Γ.𝕋₁Price_numz, Γ.𝕋₁Price_denumz, Γ.𝕋₁Price_num_addend1z, Γ.𝕋₁Price_num_addend2z]
  rw [Swap.acc_diff_t0 sw a adif]

  unfold Swap.mint
  cases (𝕋₀.toMint_t0_cases (𝕊ₐ.exists_imp_dif sw.exi)) 
  with
  | inl chooseEq
  | inr chooseEq =>
      simp [chooseEq]
      simp [Γ.mintsupply, sw.enough, le_of_lt sw.nodrain,
            𝕊ₐ.reorder_fst _ sw.t1 sw.t0,
            𝕊ₐ.reorder_snd _ sw.t1 sw.t0]
      field_simp
      ring_nf