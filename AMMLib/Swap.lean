import AMMLib.Tokens
import AMMLib.AMMSet
import AMMLib.State
import AMMLib.Supply
import AMMLib.Price

structure Swap (c: Cfg) (s: Γ) where
  t0: 𝕋₀
  t1: 𝕋₀
  a: Account
  v0: ℝ+
  enough: v0 ≤ s.atoms a t0
  exi:    s.amms.f t0 t1 ≠ 0
  nodrain: v0*(c.sx v0 (s.amms.fp exi)) < (s.amms.f t0 t1).snd

def Swap.mint (sw: Swap c s)
: 𝕋₁ := 𝕋₀.toMint (AMMSet.exists_imp_dif sw.exi)

noncomputable def Swap.apply (sw: Swap c s): Γ :=
⟨
  (s.atoms.addb sw.a sw.t1 (sw.v0*(c.sx sw.v0 (s.amms.fp sw.exi)))).subb sw.a sw.t0 sw.v0,
  s.mints,
  @AMMSet.sub_r1 (s.amms.add_r0 sw.v0 sw.exi) sw.t0 sw.t1 (sw.v0*(c.sx sw.v0 (s.amms.fp sw.exi)))

  -- Prove sw.nodrain still holds even after the add_r0
  (by simp [AMMSet.add_r0, AMMSet.exists_imp_dif sw.exi, 
            AMMSet.up]; 
      exact sw.nodrain)
⟩

/-
If an AMM is in the swap, then it was there before too.
Sketch Proof:
by cases on {t0,t1} = {sw.t0,sw.t1}
if true then trivial by Swap.exi
if false then trivial by hypothesis 
              (swap did not change this amm) 
-/
theorem Swap.amm_in_apply 
{sw: Swap c s} {t0 t1: 𝕋₀}
(h1: sw.apply.amms.f t0 t1 ≠ 0)
: s.amms.f t0 t1 ≠ 0 := by
  have hdif := AMMSet.exists_imp_dif h1
  have swhdif := AMMSet.exists_imp_dif sw.exi
  apply @Decidable.byCases (𝕋₀.toMint hdif = 𝕋₀.toMint swhdif)
  . intro minteq
    simp only [𝕋₀.toMint_eq] at minteq
    rcases minteq with ⟨t0eq,t1eq⟩|⟨t0eq,t1eq⟩
    . rw [t0eq,t1eq]
      exact sw.exi
    . rw [t0eq, t1eq]
      rw [s.amms.h1 sw.t1 sw.t0]
      simp
      exact sw.exi

  . intro mintneq
    rcases 𝕋₀.toMint_diff mintneq with ⟨left|left, right|right⟩
    <;>
    (simp [apply, AMMSet.sub_r1, AMMSet.add_r0, left, right] at h1; exact h1)

lemma Swap.mintedSupply (sw: Swap c s) (m: 𝕋₁):
  sw.apply.mintsupply m = s.mintsupply m
  := by
  simp [Γ.mintsupply, apply, Wall1.subb, Wall1.addb]


/- If an AMM existed before the swap, 
   then it exists after too. 
Sketch Proof:
by cases on {t0,t1} = {sw.t0,sw.t1}
if true,  then trivial by addition of PReal
                   and by sw.nodrain
if false, then trivial by hypothesis and
                       by same after swap -/
theorem Swap.amm_still_exists
{c: Cfg} {s: Γ} (sw: Swap c s)
{t0 t1: 𝕋₀}
(h1: s.amms.f t0 t1 ≠ 0)
: sw.apply.amms.f t0 t1 ≠ 0
:= by
  have hdif := AMMSet.exists_imp_dif h1
  have swhdif := AMMSet.exists_imp_dif sw.exi
  apply @Decidable.byCases (𝕋₀.toMint hdif = 𝕋₀.toMint swhdif)

  . intro minteq
    simp only [𝕋₀.toMint_eq] at minteq
    rcases minteq with ⟨t0eq,t1eq⟩|⟨t0eq,t1eq⟩
    . simp [apply, AMMSet.sub_r1, AMMSet.add_r0, t0eq, t1eq]
      simp only [Prod.neq_zero_iff]
      left
      simp
      simp only [t0eq, t1eq] at h1
      intro contr
      have contr' := AMMSet.exists_imp_fst h1
      contradiction
    . simp [apply, AMMSet.sub_r1, AMMSet.add_r0, t0eq, t1eq]
      simp only [Prod.neq_zero_iff]
      left
      simp [Prod.swap_ne_zero]
      exact sw.nodrain
  . intro mintneq
    rcases 𝕋₀.toMint_diff mintneq with ⟨left|left, right|right⟩
    <;>
    (simp [apply, AMMSet.sub_r1, AMMSet.add_r0, left, right]
     exact h1)

theorem Swap.amm_fp_diff (sw: Swap c s)
(t0 t1: 𝕋₀)
(exi: s.amms.f t0 t1 ≠ 0)
(hdif: (t0 ≠ sw.t0 ∨ t1 ≠ sw.t1) ∧ (t0 ≠ sw.t1 ∨ t1 ≠ sw.t0))
: sw.apply.amms.fp (sw.amm_still_exists exi)
= 
s.amms.fp exi := by
  simp [apply, AMMSet.sub_r1, AMMSet.add_r0, hdif]
  rw [AMMSet.up_diff2_pos]
  . rw [AMMSet.up_diff2_pos]
    exact hdif
  . simp [hdif, exi]

theorem Swap.minted_still_supp
{c: Cfg} {s: Γ} (sw: Swap c s)
{m: 𝕋₁}
(h1: 0 < s.mintsupply m)
: 0 < sw.apply.mintsupply m
:= by 
  unfold Γ.mintsupply at h1 ⊢
  simp [h1, apply]

theorem Swap.acc_t0_after_swap (sw: Swap c s)
: sw.apply.atoms sw.a sw.t0 
  = 
  (s.atoms sw.a sw.t0) - sw.v0
:= by simp [apply, Wall0.subb, Wall0.addb,
            AMMSet.exists_imp_dif sw.exi]

theorem Swap.acc_t1_after_swap (sw: Swap c s)
: sw.apply.atoms sw.a sw.t1 
  = 
  (s.atoms sw.a sw.t1) + (sw.v0*(c.sx sw.v0 (s.amms.fp sw.exi)))
:= by 
  simp [apply, Wall0.subb, Wall0.addb,
        (AMMSet.exists_imp_dif sw.exi).symm]

@[simp] theorem Swap.acc_r0_after_swap (sw: Swap c s)
: (sw.apply.amms.f sw.t0 sw.t1).fst
  = 
  (s.amms.f sw.t0 sw.t1).fst + sw.v0
:= by
  simp [apply, AMMSet.sub_r1, AMMSet.add_r0,
      (AMMSet.exists_imp_dif sw.exi).symm]

@[simp] theorem Swap.acc_r1_after_swap (sw: Swap c s)
: (sw.apply.amms.f sw.t0 sw.t1).snd
  = 
  (s.amms.f sw.t0 sw.t1).snd - sw.v0*(c.sx sw.v0 (s.amms.fp sw.exi))
:= by
  simp [apply, AMMSet.sub_r1, AMMSet.add_r0,
      (AMMSet.exists_imp_dif sw.exi).symm]

@[simp] theorem Swap.erase_atoms_same 
(sw: Swap c s) (a: Account)
: Finsupp.erase sw.t1 (Finsupp.erase sw.t0 (sw.apply.atoms a))
  =
  Finsupp.erase sw.t1 (Finsupp.erase sw.t0 (s.atoms a))
:= by
  ext t
  simp [apply]
  apply @Decidable.byCases (t=sw.t1)
  . intro teqt1
    simp [teqt1]
  . intro tneqt1
    apply @Decidable.byCases (t=sw.t0)
    . intro teqt0
      simp [tneqt1, teqt0, (AMMSet.exists_imp_dif sw.exi)]
    . intro tneqt0
      simp [tneqt1, tneqt0, Wall0.subb, Wall0.addb]

@[simp] theorem Γ.mintsupply_swap 
{c: Cfg} {s: Γ} {sw: Swap c s}
(m: 𝕋₁)
: sw.apply.mintsupply m = s.mintsupply m := by
simp [Swap.apply, mintsupply]

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
  simp [AMMSet.sub_r1, hdif']
  simp [AMMSet.add_r0, hdif']

@[simp] theorem swap_price_mint_diff_num_addend2z
{c: Cfg} {s: Γ} (sw: Swap c s)
(m: 𝕋₁) (hdif: m ≠ sw.mint)
: sw.apply.𝕋₁Price_num_addend2z c.o m = s.𝕋₁Price_num_addend2z c.o m := by
  simp [Γ.𝕋₁Price_num_addend2z]; left;
  simp [Swap.apply, hdif]
  rw [← 𝕋₁.choose_eq m] at hdif
  unfold Swap.mint at hdif
  have hdif' := 𝕋₀.toMint_diff hdif
  simp [AMMSet.sub_r1, hdif']
  simp [AMMSet.add_r0, hdif']


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

