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
open BigOperators

structure AMMSet where 
  map: MintedTok ⇀ AMM
  h: ∀(m: MintedTok), (h: (m ∈ map.supp)) → 
      (m.upair = (map.fh m h).f.supp)

def AMMSet.update (a: AMMSet) (v: AMM): AMMSet :=
  ⟨
  a.map.update v.toMint v, by 
  intro m hin
  apply @Decidable.byCases (m=(v.toMint))
  . intro heq
    rw [PFun.update_fh_of_self' a.map _ _ _ heq.symm]
    simp [AMM.toMint] at heq
    simp [heq]
  . intro hneq
    have hin' := a.map.in_updated_diff _ _ _ (Ne.symm hneq) hin
    rw [PFun.update_fh_of_diff a.map _ _ _ (Ne.symm hneq) 
        (hin')]
    exact a.h m hin'
  ⟩

structure MintedOf (a: AMMSet) where
  m: MintedTok
  h: m ∈ a.map.supp

def MintedOf.amm {a: AMMSet} (m: MintedOf a): AMM
  := a.map.fh m.m m.h

structure AtomicOfM {a: AMMSet} (m: MintedOf a) 
where
  t: AtomicTok
  h: t ∈ m.m.upair

def AtomicOfM.ofAMM 
  {a: AMMSet} {m: MintedOf a}
  (t: AtomicOfM m): AtomicOf (a.map.fh m.m m.h) := ⟨t.t,by 
  have h1 := t.h
  have h2 := m.h
  have h3 := a.h m.m m.h
  rw [h3] at h1; exact h1⟩