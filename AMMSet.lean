import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Algebra.BigOperators.Basic
import «Helpers»
import «PReal»
import «PFun»
import «Tokens»
import «AMM»

structure AMMSet where 
  map: MintedTok ⇀ AMM
  h: ∀(m: MintedTok), (h: (m ∈ map.supp)) → 
      (m.upair = ⟦((map.fh m h).t0, (map.fh m h).t1)⟧)

def AMMSet.map' (ammset: AMMSet) (t0 t1: AtomicTok): Option AMM :=
  if h:t0=t1 then none
  else ammset.map.f (⟨⟦(t0,t1)⟧, h⟩)

lemma map'_not_none_imp_diff 
  (ammset: AMMSet) (t0 t1: AtomicTok) 
  (exi: ammset.map' t0 t1 ≠ none)
  : t0 ≠ t1 := 
  by simp [AMMSet.map'] at exi
     let ⟨x', _⟩ := exi;
     simp; exact x'

lemma map'_not_none_imp_eq
  {ammset: AMMSet} {t0 t1: AtomicTok}
  (exi: ammset.map' t0 t1 ≠ none)
  : let minted := ⟨⟦(t0, t1)⟧, map'_not_none_imp_diff ammset t0 t1 exi⟩
    ammset.map' t0 t1 = ammset.map.f minted := by 
  
  intro minted; have hneq := map'_not_none_imp_diff ammset t0 t1 exi
  unfold AMMSet.map'; split
  next contra_eq => contradiction
  next _ => simp


lemma map'_not_none_imp_insupp
  {ammset: AMMSet} {t0 t1: AtomicTok}
  (exi: ammset.map' t0 t1 ≠ none)
  : let minted := ⟨⟦(t0, t1)⟧, map'_not_none_imp_diff ammset t0 t1 exi⟩ 
    minted ∈ ammset.map.supp := by 
    
    intro minted; have h := ammset.map.h minted
    rw [h, ← map'_not_none_imp_eq exi]
    exact exi

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
  : t0 = (ammset.map.fh ⟨⟦(t0, t1)⟧, map'_not_none_imp_diff ammset t0 t1 exi'⟩ (map'_not_none_imp_insupp exi')).t0 
  ∨ t0 = (ammset.map.fh ⟨⟦(t0, t1)⟧, map'_not_none_imp_diff ammset t0 t1 exi'⟩ (map'_not_none_imp_insupp exi')).t1
  := by
  have seth := ammset.h ⟨⟦(t0, t1)⟧, map'_not_none_imp_diff ammset t0 t1 exi'⟩ (map'_not_none_imp_insupp exi')
  simp at seth; rcases seth with ⟨t00,_⟩|⟨t01,_⟩
  . left; exact t00
  . right; exact t01

lemma amm_of_pair_imp_t1_belongs' 
  {ammset: AMMSet} {t0 t1: AtomicTok} (exi': ammset.map' t0 t1 ≠ none)
  : t1 = (ammset.map.fh ⟨⟦(t0, t1)⟧, map'_not_none_imp_diff ammset t0 t1 exi'⟩ (map'_not_none_imp_insupp exi')).t0 
  ∨ t1 = (ammset.map.fh ⟨⟦(t0, t1)⟧, map'_not_none_imp_diff ammset t0 t1 exi'⟩ (map'_not_none_imp_insupp exi')).t1
  := by
  have seth := ammset.h ⟨⟦(t0, t1)⟧, map'_not_none_imp_diff ammset t0 t1 exi'⟩ (map'_not_none_imp_insupp exi')
  simp at seth; rcases seth with ⟨_,t11⟩|⟨_,t10⟩
  . right; exact t11
  . left;  exact t10

def AMMSet.update 
  (ammset: AMMSet) (m: MintedTok) (amm: AMM)
  (h: m.upair = ⟦(amm.t0, amm.t1)⟧)
  : AMMSet := 
  ⟨ammset.map.update m amm,
  /- We must prove, for this updated ammset, 
     ∀{m: MintedTok}, (h: (m ∈ map.supp)) → 
      (m.upair = ⟦((map.fh h).t0, (map.fh h).t1)⟧)
    Choose m' and assume it is in updated.supp[H]
    Then, by cases on m'=m:
      if m'=m, then it is trivial by the definition of update
      otherwise, it must be in old.supp
      and updated.f m' = old.f m'
      then apply old.h -/
   by intro m' h'; have h'' := h'; simp [PFun.update] at h'';
      apply @Decidable.byCases (m'=m)
      . intro heq; have heq' := heq.symm;
        rw [PFun.update_fh_of_self' ammset.map m amm m' heq']
        rw [heq]; exact h
      . intro hneq; have hin := Or.exclude_left h'' hneq
        rw [← ne_eq] at hneq
        rw [PFun.update_fh_of_diff ammset.map m amm m' hneq.symm hin];
        exact ammset.h m' hin
  ⟩


def get_amm {s: AMMSet} {t0 t1: AtomicTok} (exi: s.map' t0 t1 ≠ none): AMM
  := (s.map.fh ⟨⟦(t0, t1)⟧, map'_not_none_imp_diff s t0 t1 exi⟩ (map'_not_none_imp_insupp exi))

lemma get_amm_lemma 
  {s: AMMSet} {t0 t1: AtomicTok} (exi: s.map' t0 t1 ≠ none)
  : (⟨⟦(t0, t1)⟧, map'_not_none_imp_diff s t0 t1 exi⟩: MintedTok).upair
    =
    ⟦((get_amm exi).t0, (get_amm exi).t1)⟧ := by 
    simp [get_amm]
    have insupp := map'_not_none_imp_insupp exi
    have h := s.h ⟨⟦(t0, t1)⟧, map'_not_none_imp_diff s t0 t1 exi⟩ insupp
    simp at h
    aesop

def get_r0 {s: AMMSet} {t0 t1: AtomicTok} (exi: s.map' t0 t1 ≠ none): ℝ+
  := (get_amm exi).r t0 (amm_of_pair_imp_t0_belongs' exi)

def get_r1 {s: AMMSet} {t0 t1: AtomicTok} (exi: s.map' t0 t1 ≠ none): ℝ+
  := (get_amm exi).r t1 (amm_of_pair_imp_t1_belongs' exi)