import Mathlib.Tactic.LibrarySearch
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Real.NNReal
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Algebra.BigOperators.Basic
import «Helpers»
import «PReal»
import «Tokens»
import «AMMSet»
open Token

abbrev State        := AccountSet × AMMSet
def State.accounts (s: State) := s.fst
abbrev State.amms     (s: State) := s.snd
def State.amm (s: State) (amm: MintedTok) := (s.snd).map amm

def SwapRate := PReal → PReal → PReal → PReal
noncomputable def constprod: SwapRate := λ x r0 r1 => r1 / (r0 + x)

def swap_amount (sx: SwapRate) (x r0 r1: PReal)
  := x*(sx x r0 r1)

noncomputable def swap0
  (sx: SwapRate) (a: Account) 
  (v0: PReal) (t0 t1: AtomicTok) (s: State)
  (_: v0.1 ≤ (s.accounts a) t0) /- UNUSED MINIMUM BALANCE PRECONDITION -/
  (exi: s.amms.map' t0 t1 ≠ none)
  (nodrain: swap_amount sx v0 ((δ (s.amms.map' t0) t1 exi).r t0 (amm_of_pair_imp_t0_belongs' exi)) ((δ (s.amms.map' t0) t1 exi).r t1 (amm_of_pair_imp_t1_belongs' exi)) < (δ (s.amms.map' t0) t1 exi).r t1 (amm_of_pair_imp_t1_belongs' exi))
  : State :=
  let ht   := map'_not_none_imp_diff s.amms t0 t1 exi
  let ht0  := amm_of_pair_imp_t0_belongs' exi
  let ht1  :=  amm_of_pair_imp_t1_belongs' exi
  let r0   := (δ (s.amms.map' t0) t1 exi).r t0 ht0
  let r1   := (δ (s.amms.map' t0) t1 exi).r t1 ht1
  let swam := swap_amount sx v0 r0 r1
  let w    := s.accounts a
  let w'   := w.update (Atomic t0) ((w (Atomic t0)) - v0.toNNReal)
  let w''  := w'.update (Atomic t1) ((w' (Atomic t1)) + swam)
  let amm  := δ (s.amms.map' t0) t1 exi
  let amm' := amm.sub t1 swam ht1 nodrain
  let ht0' := AMM.sub.still_belongs ht1 nodrain t0 ht0
  let amm'':= amm'.add t0 v0 (AMM.sub.still_belongs ht1 nodrain t0 ht0)

  (s.accounts.update a w'',
  ⟨Function.update s.amms.map ⟨⟦(t0,t1)⟧,ht⟩ (some amm''),
   by intro m a; unfold Function.update; split;
      /- m is equal to the mintedtoken we just updated -/
      next meq => 
        intro h;
        have h': amm'' = a := by simp at h; exact h
        rw [← h']; 
        rw [← AMM.add.t0_same v0 ht0']
        rw [← AMM.sub.t0_same ht1 nodrain]
        rw [← AMM.add.t1_same v0 ht0']
        rw [← AMM.sub.t1_same ht1 nodrain]
        rw [AMMSet.δ_map'_property (State.amms s) t0 t1 exi]
        simp [meq]
      /- m is different: Function.update uses the old ammset
         So we use its proof -/
      next mneq =>
        intro h
        exact (State.amms s).h m a h
  ⟩)