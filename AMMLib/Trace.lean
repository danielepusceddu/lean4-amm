import AMMLib.Deposit
import AMMLib.State
import AMMLib.Tokens
import AMMLib.Swap
import AMMLib.Price
import AMMLib.Networth

/- Tx c init s is the type of all possible sequences of transactions
  that would result in s, starting from Γ init and using configuration c -/
inductive Tx (c: Cfg) (init: Γ): Γ → Type where
  | empty: Tx c init init

  | dep0 (s': Γ) (rs: Tx c init s') (d: Deposit0 s'): 
      Tx c init d.apply

  | swap (s': Γ) (rs: Tx c init s') (sw: Swap c s'):
      Tx c init sw.apply

def reachableInit (s: Γ): Prop :=
  (s.amms = 𝕊ₐ.empty ∧ ∀ (a: 𝔸) (m: 𝕋₁), s.mints a m = 0)

def reachable (c: Cfg) (s: Γ): Prop :=
  ∃ (init: Γ) (tx: Tx c init s), reachableInit init

def concat {c: Cfg} {init s' s'': Γ} 
(t1: Tx c init s') (t2: Tx c s' s''): Tx c init s'' := match t2 with
  | Tx.empty => t1
  | Tx.dep0 ds rs d => Tx.dep0 ds (concat t1 rs) d
  | Tx.swap ds rs sw => Tx.swap ds (concat t1 rs) sw

/-
Proof that 
m ∈ (Trace c s).Γ.amms.map.supp → supply m > 0

by induction
empty (base case): hypothesis is a contradiction
dep0: trivial by cases on the deposited tokens:
      if the pair is the same, then the supply is positive.
      if the pair isn't the same, the supply is the same as
      before and we can use IH.
swap: use IH. 
      swaps don't change minted token supplies
-/

theorem AMMimpSupplyProp
{c: Cfg} {s: Γ} (r: reachable c s) {t0 t1: 𝕋₀}
(h: s.amms.f t0 t1 ≠ 0)
: 0 < s.mintsupply (𝕋₀.toMint (𝕊ₐ.exists_imp_dif h)) := by
  have ⟨init, tx, ⟨init_amms, init_accs⟩⟩ := r
  induction tx with
  | empty => 
      exfalso
      simp [init_amms, 𝕊ₐ.empty] at h

  | dep0 sprev tail d ih =>
    apply @Decidable.byCases ((𝕋₀.toMint (𝕊ₐ.exists_imp_dif h))=(𝕋₀.toMint d.hdif))
    . intro eq; rw [eq]
      simp [Deposit0.apply, Γ.mintsupply, eq]
      left
      exact d.r0.coe_pos
    
    . intro neq
      simp [neq]
      simp [𝕋₀.toMint_diff neq] at h
      have re: reachable c sprev := by
        exists init; exists tail
      exact ih re h
  
  | swap sprev tail sw ih =>
      rw [Swap.mintedSupply]
      have h' := Swap.amm_in_apply h
      have re: reachable c sprev := by
        exists init; exists tail
      exact ih re h'

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