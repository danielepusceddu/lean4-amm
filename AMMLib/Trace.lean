import AMMLib.Deposit
import AMMLib.State
import AMMLib.Tokens
import AMMLib.Swap
import AMMLib.Price

/- Tx c init s is the type of all possible sequences of transactions
  that would result in s, starting from state init and using configuration c -/
inductive Tx (c: Config) (init: State): State → Type where
  | empty: Tx c init init

  | dep0 (s': State) (rs: Tx c init s') (d: Deposit0 s'): 
      Tx c init d.apply

  | swap (s': State) (rs: Tx c init s') (sw: Swap c s'):
      Tx c init sw.apply

def reachableInit (s: State): Prop :=
  (s.amms = AMMSet.empty ∧ ∀ (a: Account) (m: MintedTok), s.mints a m = 0)

def reachable (c: Config) (s: State): Prop :=
  ∃ (init: State) (tx: Tx c init s), reachableInit init

def concat {c: Config} {init s' s'': State} 
(t1: Tx c init s') (t2: Tx c s' s''): Tx c init s'' := match t2 with
  | Tx.empty => t1
  | Tx.dep0 ds rs d => Tx.dep0 ds (concat t1 rs) d
  | Tx.swap ds rs sw => Tx.swap ds (concat t1 rs) sw

/-
Proof that 
m ∈ (Trace c s).state.amms.map.supp → supply m > 0

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
{c: Config} {s: State} (r: reachable c s) {t0 t1: AtomicTok}
(h: s.amms.f t0 t1 ≠ 0)
: 0 < s.mintsupply (AtomicTok.toMint (AMMSet.exists_imp_dif h)) := by
  have ⟨init, tx, ⟨init_amms, init_accs⟩⟩ := r
  induction tx with
  | empty => 
      exfalso
      simp [init_amms, AMMSet.empty] at h

  | dep0 sprev tail d ih =>
    apply @Decidable.byCases ((AtomicTok.toMint (AMMSet.exists_imp_dif h))=(AtomicTok.toMint d.hdif))
    . intro eq; rw [eq]
      simp [Deposit0.apply, State.mintsupply, eq]
      left
      exact d.r0.coe_pos
    
    . intro neq
      simp [neq]
      simp [AtomicTok.toMint_diff neq] at h
      have re: reachable c sprev := by
        exists init; exists tail
      exact ih re h
  
  | swap sprev tail sw ih =>
      rw [Swap.mintedSupply]
      have h' := Swap.amm_in_apply h
      have re: reachable c sprev := by
        exists init; exists tail
      exact ih re h'

noncomputable def State.mintedPrice 
{s: State} {c: Config} (r: reachable c s)
(m: MintedTok) (h: s.amms.f m.choose m.other ≠ 0)
: ℝ+ :=
s.mintedTokPrice c m h (by have h' := AMMimpSupplyProp r h; simp at h'; exact h')

def atomicworth 
(o: AtomicTok → PReal) (t: AtomicTok) (x: NNReal)
: NNReal := (o t)*x

noncomputable def AtomicWall.networth
(w: AtomicTok →₀ NNReal) (o: AtomicTok → PReal): NNReal :=
w.sum (atomicworth o)

noncomputable def mintedworth
(s: State) (o: AtomicTok → PReal) (t: MintedTok) (x: NNReal)
: NNReal := (s.mintedTokPricez o t)*x

noncomputable def MintedWall.networth
(w: MintedTok →₀ NNReal) (s: State) (o: AtomicTok → PReal): NNReal :=
w.sum (mintedworth s o)

noncomputable def State.networth
(s: State) (a: Account) (o: AtomicTok → PReal): NNReal
:=
(AtomicWall.networth (s.atoms a) o)
+
(MintedWall.networth (s.mints a) s o)

noncomputable def Account.gain
{c: Config} {s s': State} (a: Account) (_: Tx c s s')
: ℝ
:= ((s'.networth a c.o): ℝ) - ((s.networth a c.o): ℝ)

theorem lemma32_same
{c: Config} {s: State} {sw: Swap c s} (tx: Tx c s (sw.apply))
: 
(sw.a.gain tx)
=
sw.v0*((c.sx sw.v0 (s.amms.fp sw.exi))*(c.o sw.t1) - (c.o sw.t0))*(1 - (s.mints sw.a (AtomicTok.toMint (AMMSet.exists_imp_dif sw.exi)))/(s.mints.supply (AtomicTok.toMint (AMMSet.exists_imp_dif sw.exi))))
:= by sorry