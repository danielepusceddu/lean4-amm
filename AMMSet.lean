import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Algebra.BigOperators.Basic
import «Helpers»
import «PReal»
import «Tokens»
import «AMM»

structure AMMSet where 
  map: MintedTok → Option AMM
  h: ∀(m: MintedTok) (a: AMM), 
      (map m = some a) → (m.upair = ⟦(a.t0, a.t1)⟧)

def AMMSet.map' (ammset: AMMSet) (t0 t1: AtomicTok): Option AMM :=
  if h:t0=t1 then none
  else ammset.map (⟨⟦(t0,t1)⟧, h⟩)

lemma map'_not_none_imp_diff 
  (ammset: AMMSet) (t0 t1: AtomicTok) 
  (exi: ammset.map' t0 t1 ≠ none)
  : t0 ≠ t1 := 
  by simp [AMMSet.map'] at exi
     let ⟨x', _⟩ := exi;
     simp; exact x'

lemma map'_not_none_imp_map_not_none 
  (ammset: AMMSet) (t0 t1: AtomicTok) 
  (exi: ammset.map' t0 t1 ≠ none)
  : ammset.map ⟨⟦(t0, t1)⟧, map'_not_none_imp_diff ammset t0 t1 exi⟩ ≠ none := 
  by simp [AMMSet.map'] at exi
     let ⟨_, h⟩ := exi;
     exact h

lemma map'_unordered 
  (ammset: AMMSet) (t0 t1: AtomicTok)
  : ammset.map' t0 t1 = ammset.map' t1 t0
  := by simp [AMMSet.map']
        split; 
        next heq => have heq' := Eq.symm heq; 
                    split; rfl; rfl
        next neq => have neq' := Ne.symm neq; simp at neq';
                    split; next contra => contradiction
                    next neq2' => simp_rw [Sym2.eq_swap]

lemma amm_of_pair_imp_t0_belongs' 
  {ammset: AMMSet} {t0 t1: AtomicTok} (exi': ammset.map' t0 t1 ≠ none)
  :
  t0 = (δ (ammset.map' t0) t1 exi').t0 
  ∨ t0 = (δ (ammset.map' t0) t1 exi').t1
  := by
      let ht  := map'_not_none_imp_diff ammset t0 t1 exi'
      let ht' := option_imply (ammset.map' t0 t1) exi'
      let ⟨amm,hamm⟩ := ht'
      have hamm' := δ_def (ammset.map' t0) t1 (amm) (hamm)
      simp
      rw [hamm']
      have hamm'' := ammset.h ⟨⟦(t0, t1)⟧, ht⟩ amm
      simp [AMMSet.map', ht] at hamm
      have hamm''' := hamm'' hamm
      simp at hamm'''
      rcases hamm''' with ⟨h11,_⟩|⟨h21,_⟩
      . apply Or.inl; exact h11
      . apply Or.inr; exact h21

lemma amm_of_pair_imp_t1_belongs' 
  {ammset: AMMSet} {t0 t1: AtomicTok} (exi': ammset.map' t0 t1 ≠ none)
  :
  t1 = (δ (ammset.map' t0) t1 exi').t0 
  ∨ t1 = (δ (ammset.map' t0) t1 exi').t1 := by 
    have exi: ammset.map' t1 t0 ≠ none :=
      by rw [map'_unordered]; exact exi'
    have u := amm_of_pair_imp_t0_belongs' exi
    unfold δ at u; split at u;
    next uamm uh => 
      simp;
      unfold δ; split
      next gamm gh => rw [map'_unordered] at gh
                      simp [uh] at gh
                      simp [← gh]; exact u
      next contra => rw [map'_unordered] at contra; contradiction
    next contra => contradiction

lemma AMMSet.δ_map'_property 
  (ammset: AMMSet) (t0 t1: AtomicTok)
  (h: ammset.map' t0 t1 ≠ none)
  : ⟦((δ (ammset.map' t0) t1 h).t0,
     (δ (ammset.map' t0) t1 h).t1)⟧ = (⟦(t0, t1)⟧: Sym2 AtomicTok):= by 
  unfold δ; split
  next amm hamm => 
    unfold map' at hamm; split at hamm
    next contra => contradiction
    next hneq => 
      rw [← ne_eq] at hneq
      have h' := ammset.h ⟨⟦(t0,t1)⟧, hneq⟩ amm hamm
      symm; exact h'
  next contra => contradiction

    
def AMMSet.r (ammset: AMMSet) (t0 t1: AtomicTok) (exi': ammset.map' t0 t1 ≠ none): PReal × PReal :=
  -- First: reserves of t0
  ((δ (ammset.map' t0) t1 (exi')).r t0 
    (amm_of_pair_imp_t0_belongs' exi'),
  
  -- Second: reserves of t1
  (δ (ammset.map' t0) t1 (exi')).r t1
    (amm_of_pair_imp_t1_belongs' exi'))