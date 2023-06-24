import AMMLib.Tokens
import AMMLib.AMMSet
import AMMLib.State
import AMMLib.Supply
import AMMLib.Price

structure Swap 
  (sx: SX) (o: 𝕆) (s: Γ) (a: 𝔸) (t0 t1: 𝕋₀) (v0: ℝ+) 
  where
  enough: v0 ≤ s.atoms a t0
  exi: s.amms.init t0 t1
  nodrain: v0*(sx v0 (s.amms.r0 t0 t1 exi) (s.amms.r1 t0 t1 exi)) < (s.amms.r1 t0 t1 exi)

@[simp] theorem Swap.init (sw: Swap sx o s a t0 t1 v0):
  s.amms.init t0 t1 := by sorry

def Swap.y (sw: Swap sx o s a t0 t1 v0): ℝ+
  := v0*(sx v0 (s.amms.r0 t0 t1 sw.exi) (s.amms.r1 t0 t1 sw.exi))

/-
def Swap.hdif (sw: Swap sx o s a t0 t1 v0):
t0 ≠ t1 := 𝕊ₐ.exists_imp_dif sw.exi

def Swap.mint (sw: Swap sx o s a t0 t1 v0)
: 𝕋₁ := 𝕋₀.toMint sw.hdif

def Swap.exi_swap (sw: Swap sx o s a t0 t1 v0):
  s.amms.f t1 t0 ≠ 0 :=
    𝕊ₐ.exists_swap sw.exi
-/

noncomputable def Swap.apply (sw: Swap sx o s a t0 t1 v0): Γ :=
⟨
  (s.atoms.addb a t1 sw.y).subb a t0 v0,
  s.mints,
  (s.amms.sub_r1 t0 t1 sw.exi sw.y sw.nodrain).add_r0 t0 t1 (by simp[sw.exi]) v0
⟩

@[simp] theorem 𝕊ₐ.init_of_swap (sw: Swap sx o s a t0 t1 v0)
  (t0' t1': 𝕋₀):
  sw.apply.amms.init t0' t1' ↔ s.amms.init t0' t1' := by
    unfold Swap.apply
    simp

@[simp] theorem Swap.r0_self
  (sw: Swap sx o s a t0 t1 v0):
  (sw.apply).amms.r0 t0 t1 (by simp[sw.exi]) = v0 + s.amms.r0 t0 t1 sw.exi := by 
  unfold apply;
  simp [sw.init]

@[simp] theorem Swap.r1_self
  (sw: Swap sx o s a t0 t1 v0):
  (sw.apply).amms.r1 t0 t1 (by simp[sw.exi]) = (s.amms.r1 t0 t1 sw.exi).sub sw.y (sw.nodrain) := by 
  unfold apply;
  simp [sw.init]

@[simp] theorem Swap.b0_self
  (sw: Swap sx o s a t0 t1 v0):
  (sw.apply).atoms a t0 = s.atoms a t0 - v0 := by
  unfold apply
  simp
  sorry

@[simp] theorem Swap.b1_self
  (sw: Swap sx o s a t0 t1 v0):
  (sw.apply).atoms a t1 = sw.y + s.atoms a t1 := by
  unfold apply
  simp
  sorry

def Swap.inv 
  (sw: Swap sx o s a t0 t1 v0)
  (hbound: SX.outputbound sx)
  (hrev: SX.reversible sx hbound)
  : Swap sx o sw.apply a t1 t0 sw.y
  := by sorry

theorem Swap.inv_y_eq_x
  (sw: Swap sx o s a t0 t1 x)
  (hbound: SX.outputbound sx)
  (hrev: SX.reversible sx hbound)
  : (sw.inv hbound hrev).y = x := by 
  unfold y
  rw [𝕊ₐ.r0_reorder _ t1 t0 _,
      𝕊ₐ.r1_reorder _ t1 t0 _]
  rw [mul_assoc]
  unfold SX.reversible at hrev
  simp [y, hrev]

@[simp] theorem Swap.mintsupply
  (sw: Swap sx o s a t0 t1 v0)
  (m: 𝕋₁): 
  sw.apply.mintsupply m = s.mintsupply m := by
  simp [Swap.apply, Γ.mintsupply]

/-
If an AMM is in the swap, then it was there before too.
Sketch Proof:
by cases on {t0,t1} = {sw.t0,sw.t1}
if true then trivial by Swap.exi
if false then trivial by hypothesis 
              (swap did not change this amm) 
-/

/- If an AMM existed before the swap, 
   then it exists after too. 
Sketch Proof:
by cases on {t0,t1} = {sw.t0,sw.t1}
if true,  then trivial by addition of PReal
                   and by sw.nodrain
if false, then trivial by hypothesis and
                       by same after swap -/

/-
theorem Swap.amm_still_exists
(sw: Swap sx o s a t0 t1 v0)
{t0' t1': 𝕋₀}
(h1: s.amms.f t0' t1' ≠ 0)
: sw.apply.amms.f t0' t1' ≠ 0
:= by
  have hdif := 𝕊ₐ.exists_imp_dif h1
  have swhdif := sw.hdif
  apply @Decidable.byCases (𝕋₀.toMint hdif = 𝕋₀.toMint swhdif)

  . intro minteq
    simp only [𝕋₀.toMint_eq] at minteq
    rcases minteq with ⟨t0eq,t1eq⟩|⟨t0eq,t1eq⟩
    . simp [apply, 𝕊ₐ.sub_r1, 𝕊ₐ.add_r0, t0eq, t1eq]
      simp only [Prod.neq_zero_iff]
      left
      simp
      simp only [t0eq, t1eq] at h1
      intro contr
      have contr' := 𝕊ₐ.exists_imp_fst h1
      contradiction
    . simp [apply, 𝕊ₐ.sub_r1, 𝕊ₐ.add_r0, t0eq, t1eq]
      simp only [Prod.neq_zero_iff]
      left
      simp [Prod.swap_ne_zero]
      exact sw.nodrain
  . intro mintneq
    rcases 𝕋₀.toMint_diff mintneq with ⟨left|left, right|right⟩
    <;>
    (simp [apply, 𝕊ₐ.sub_r1, 𝕊ₐ.add_r0, left, right]
     exact h1)


lemma Swap.mintedSupply (sw: Swap sx o s a t0 t1 v0) (m: 𝕋₁):
  sw.apply.mintsupply m = s.mintsupply m
  := by
  simp [Γ.mintsupply, apply, 𝕊₁.subb, 𝕊₁.addb]

theorem Swap.amm_fp_diff (sw: Swap sx o s a t0 t1 v0)
(t0' t1': 𝕋₀)
(exi: s.amms.f t0' t1' ≠ 0)
(hdif: (t0' ≠ t0 ∨ t1' ≠ t1) ∧ (t0' ≠ t1 ∨ t1' ≠ t0))
: sw.apply.amms.fp (sw.amm_still_exists exi)
= 
s.amms.fp exi := by
  simp [apply, 𝕊ₐ.sub_r1, 𝕊ₐ.add_r0, hdif]
  rw [𝕊ₐ.up_diff2_pos]
  . rw [𝕊ₐ.up_diff2_pos]
    exact hdif
  . simp [hdif, exi]

theorem Swap.minted_still_supp
{c: Cfg} {s: Γ} (sw: Swap sx o s a t0 t1 v0)
{m: 𝕋₁}
(h1: 0 < s.mintsupply m)
: 0 < sw.apply.mintsupply m
:= by 
  unfold Γ.mintsupply at h1 ⊢
  simp [h1, apply]

theorem Swap.acc_t0_after_swap (sw: Swap sx o s a t0 t1 v0)
: sw.apply.atoms a t0 
  = 
  (s.atoms a t0) - v0
:= by simp [apply, 𝕊₀.subb, 𝕊₀.addb,
            sw.hdif]

@[simp] theorem Swap.acc_diff_t0 
(sw: Swap sx o s a t0 t1 v0) (a': 𝔸) (hdif: a' ≠ a):
sw.apply.atoms a' = s.atoms a' := by
  ext t
  simp [apply, 𝕊₀.subb, 𝕊₀.addb, hdif]

@[simp] theorem Swap.acc_diff_t1
(sw: Swap sx o s a t0 t1 v0) (a': 𝔸) (hdif: a' ≠ a):
sw.apply.mints a' = s.mints a' := by
  ext t
  simp [apply, 𝕊₀.subb, 𝕊₀.addb, hdif]

theorem Swap.acc_t1_after_swap (sw: Swap sx o s a t0 t1 v0)
: sw.apply.atoms a t1 
  = 
  (s.atoms a t1) + (v0*(sx v0 (s.amms.fp sw.exi).fst (s.amms.fp sw.exi).snd))
:= by 
  simp [apply, 𝕊₀.subb, 𝕊₀.addb,
        sw.hdif.symm]

@[simp] theorem Swap.acc_r0_after_swap (sw: Swap sx o s a t0 t1 v0)
: (sw.apply.amms.f t0 t1).fst
  = 
  (s.amms.f t0 t1).fst + v0
:= by
  simp [apply, 𝕊ₐ.sub_r1, 𝕊ₐ.add_r0,
      sw.hdif.symm]

@[simp] theorem Swap.acc_r1_after_swap (sw: Swap sx o s a t0 t1 v0)
: (sw.apply.amms.f t0 t1).snd
  = 
  (s.amms.f t0 t1).snd - (v0*(sx v0 (s.amms.fp sw.exi).fst (s.amms.fp sw.exi).snd))
:= by
  simp [apply, 𝕊ₐ.sub_r1, 𝕊ₐ.add_r0,
      sw.hdif.symm]

@[simp] theorem Swap.erase_atoms_same 
(sw: Swap sx o s a t0 t1 v0) (a: 𝔸)
: Finsupp.erase t1 (Finsupp.erase t0 (sw.apply.atoms a))
  =
  Finsupp.erase t1 (Finsupp.erase t0 (s.atoms a))
:= by
  ext t
  simp [apply]
  apply @Decidable.byCases (t=t1)
  . intro teqt1
    simp [teqt1]
  . intro tneqt1
    apply @Decidable.byCases (t=t0)
    . intro teqt0
      simp [tneqt1, teqt0, sw.hdif]
    . intro tneqt0
      simp [tneqt1, tneqt0, 𝕊₀.subb, 𝕊₀.addb]

@[simp] theorem Γ.mintsupply_swap 
(sw: Swap sx o s a t0 t1 v0)
(m: 𝕋₁)
: sw.apply.mintsupply m = s.mintsupply m := by
simp [Swap.apply, mintsupply]
-/