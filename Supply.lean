import «Tokens»
import «AMMSet»
import «State»
open BigOperators

/- It's important to use 'rev' here because
   mathlib theorems use the form:
   ∑ x in s, f x
   So using (as a) t would be bad as a wouldn't be the last parameter.
-/
def AccountSet.supply (as: AccountSet) (t: Token): NNReal :=
  ∑ a in as.support, as.rev t a

/- Lemma supply_update_diff
   Given an AccountSet that had one of its wallets updated
   by a single token, the supplies of all other tokens remain the same. 
-/ /-
Informal proof 
Useful1: theorem Finset.sum_insert_of_eq_zero_if_not_mem
        (h : ¬a ∈ s → f a = 0)
        (Finset.sum (insert a s) fun x => f x) = Finset.sum s fun x => f x

Useful2: theorem Finset.sum_erase
         (h : f a = 0)
         (Finset.sum (Finset.erase s a) fun x => f x) = Finset.sum s fun x => f x
rev_update_diff: ((as.update a ((as a).update t' v)).rev t) = as.rev t

supply (as.update a ((as a).update t' v)) t
∑ (as.update a ((as a).update t' v)).support ((as.update a ((as a).update t' v)).rev t)   by supply

∑ (as.update a ((as a).update t' v)).support (as.rev t)   by rev_update_diff
case ((as a).update t' v) ≠ 0
  ∑ (insert a in as.support) (as.rev t)   by support of update ≠ 0
  apply Useful1 
  ∑ as.support (as.rev t)
case ((as a).update t' v) = 0
  ∑ (erase a in as.support) (as.rev t)    by support of update = 0
  apply Useful 2 (remember t ≠ t': if update of t' makes it 0, then everything else was already 0, including t.)
  ∑ as.support (as.rev t) 
Qed -/
lemma AccountSet.supply_update_diff (as: AccountSet) (t: Token) (a: Account) (t': Token) (v: NNReal) (hdif: t ≠ t'):
  supply (as.update a ((as a).update t' v)) t = as.supply t := by 
  unfold supply
  conv in (fun _ => _) => 
    intro a1
    rw [rev_update_diff _ _ _ _ _ _ hdif]
  apply @Decidable.byCases ((Finsupp.update (as a) t' v) = 0)
  . intro eq0
    rw [eq0, Finsupp.support_update_zero]
    have l1: rev as t a = 0 := by 
      unfold rev;
      rw [Finsupp.update_is_zero (as a) _ _ eq0]
      exact (Finsupp.single_eq_of_ne hdif.symm)
    rw [Finset.sum_erase as.support l1]
  . intro neq0
    rw [Finsupp.support_update_ne_zero _ _ neq0]
    have l1 := rev_account_not_mem as t a
    rw [Finset.sum_insert_of_eq_zero_if_not_mem l1]

noncomputable def AMMSet.supply (amms: AMMSet) (t: AtomicTok): NNReal :=
  amms.map.sum (λ amm => 
    if h:t ∈ amm.f.supp
    then amm.r0 ⟨t, h⟩
    else 0)

noncomputable def State.supply (s: State) (t: Token): NNReal
  := match t with
  | Token.Atomic t' => (s.accs.supply t) + (s.amms.supply t')
  | Token.Minted _ => s.accs.supply t

noncomputable def State.redeemrate
  (s: State) (m: MintedOf s.amms) (t: AtomicOfM m): NNReal
  := (m.amm.r0 t.ofAMM) / (s.supply m.m)