import AMMLib.Supply
import AMMLib.Swap

noncomputable def State.mintedTokPrice_denum
(s: State) (m: MintedTok)
(h2: 0 < s.mintsupply m): ℝ+ := ⟨s.mintsupply m, h2⟩

noncomputable def State.mintedTokPrice_num_addend1
(s: State) (c: Config)
(m: MintedTok) (h1: s.amms.f m.choose m.other ≠ 0)
: ℝ+ := (s.amms.fp h1).fst * (c.o m.choose)

noncomputable def State.mintedTokPrice_num_addend2
(s: State) (c: Config)
(m: MintedTok) (h1: s.amms.f m.choose m.other ≠ 0)
: ℝ+ := (s.amms.fp h1).snd * (c.o m.other)

noncomputable def State.mintedTokPrice_num
(s: State) (c: Config)
(m: MintedTok) (h1: s.amms.f m.choose m.other ≠ 0)
: ℝ+ :=
(s.mintedTokPrice_num_addend1 c m h1) + (s.mintedTokPrice_num_addend2 c m h1)

noncomputable def State.mintedTokPrice 
(s: State) (c: Config)
(m: MintedTok) (h1: s.amms.f m.choose m.other ≠ 0)
(h2: 0 < s.mintsupply m)
: ℝ+ :=
(s.mintedTokPrice_num c m h1) / (s.mintedTokPrice_denum m h2)

@[simp] lemma Swap.mintedTokPrice_denum_diff
{c: Config} {s: State} (sw: Swap c s) 
(m: MintedTok) (h2: 0 < s.mintsupply m)
: sw.apply.mintedTokPrice_denum m ((sw.minted_still_supp h2)) = s.mintedTokPrice_denum m h2
:= by 
unfold State.mintedTokPrice_denum
apply Subtype.eq; simp
simp [Swap.mintedSupply]

@[simp] lemma Swap.mintedTokPrice_num_addend1_diff
{c: Config} {s: State} (sw: Swap c s) 
(m: MintedTok) (h1: s.amms.f m.choose m.other ≠ 0)
(hdif: m ≠ AtomicTok.toMint (AMMSet.exists_imp_dif sw.exi))
: sw.apply.mintedTokPrice_num_addend1 c m (sw.amm_still_exists h1) = s.mintedTokPrice_num_addend1 c m h1
:= by 
unfold State.mintedTokPrice_num_addend1
rw [← MintedTok.choose_eq m] at hdif
have hdif' := AtomicTok.toMint_diff hdif
simp [h1, hdif', Swap.amm_fp_diff]

@[simp] lemma Swap.mintedTokPrice_num_addend2_diff
{c: Config} {s: State} (sw: Swap c s) 
(m: MintedTok) (h1: s.amms.f m.choose m.other ≠ 0)
(hdif: m ≠ AtomicTok.toMint (AMMSet.exists_imp_dif sw.exi))
: sw.apply.mintedTokPrice_num_addend2 c m (sw.amm_still_exists h1) = s.mintedTokPrice_num_addend2 c m h1
:= by 
unfold State.mintedTokPrice_num_addend2
rw [← MintedTok.choose_eq m] at hdif
have hdif' := AtomicTok.toMint_diff hdif
simp [h1, hdif', Swap.amm_fp_diff]

@[simp] lemma Swap.mintedTokPrice_num_diff
{c: Config} {s: State} (sw: Swap c s) 
(m: MintedTok) (h1: s.amms.f m.choose m.other ≠ 0)
(hdif: m ≠ AtomicTok.toMint (AMMSet.exists_imp_dif sw.exi))
: sw.apply.mintedTokPrice_num c m (sw.amm_still_exists h1) = s.mintedTokPrice_num c m h1
:= by 
unfold State.mintedTokPrice_num
simp [h1, hdif]

@[simp] theorem Swap.mintedTokPrice_diff 
(c: Config) (s: State) (sw: Swap c s) 
(m: MintedTok) (h1: s.amms.f m.choose m.other ≠ 0)
(h2: 0 < s.mintsupply m)
(hdif: m ≠ AtomicTok.toMint (AMMSet.exists_imp_dif sw.exi))
: 
(sw.apply.mintedTokPrice c m (sw.amm_still_exists h1) (sw.minted_still_supp h2)) 
=
(s.mintedTokPrice c m h1 h2)
:= by 
unfold State.mintedTokPrice
simp [h1, h2, hdif]