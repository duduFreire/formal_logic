import tactic 
import order.zorn

variable {α : Type*}

lemma max_of_fin_chain [partial_order α]
: ∀{c : set α}, c.finite → is_chain (≤) c → c.nonempty → ∃m ∈ c, ∀{b}, b ∈ c → b ≤ m :=
begin 
	intros c c_fin c_chain c_nonempty,
	rcases finset.exists_maximal (set.finite.to_finset c_fin) 
	((set.finite.nonempty_to_finset c_fin).mpr c_nonempty) with ⟨m, hmc, hm⟩,
	have hmc' :=(set.finite.mem_to_finset c_fin).mp hmc,
	use [m, hmc'],
	intros b hbc,
	specialize hm b ((set.finite.mem_to_finset c_fin).mpr hbc),
	unfold is_chain set.pairwise at c_chain,
	specialize c_chain hbc hmc',
	by_cases hbm : b = m,
	{exact (eq.symm hbm).ge},
	{
		cases c_chain hbm, exact h, exfalso,
		exact hm ((ne.symm hbm).lt_of_le h),
	}
end

def finite_character (F : set (set α)) : Prop :=
 ∀ X, X ∈ F ↔ (∀{Y : set α}, Y ⊆ X → Y.finite → Y ∈ F)

variable {F : set (set α)}

lemma mem_empty_of_fin_character : 
F.nonempty → finite_character F → ∅ ∈ F :=
begin
	intros F_nonempty F_fin_char,
	cases F_nonempty with X hX,
	exact (F_fin_char X).mp hX (set.empty_subset X) set.finite_empty,
end

lemma exists_maximal_of_finite_character {X} (hX : X ∈ F) :
 finite_character F → ∃M ∈ F, X ⊆ M ∧ ∀{Y}, Y ∈ F → M ⊆ Y → Y = M :=
 begin 
	intro F_fin_char,
	apply zorn_subset_nonempty, swap, exact hX,

	intros c c_ss c_chain c_nonempty,
	use c.sUnion,

	split, swap, {exact λs hs, set.subset_sUnion_of_mem hs},
	by_contra hUcF,
	rw F_fin_char c.sUnion at hUcF, push_neg at hUcF,
	rcases hUcF with ⟨Y, Y_ss, Y_fin, hYF⟩,
	suffices : ∃b ∈ c, b ∉ F,	{rcases this with ⟨b, hb1, hb2⟩, exact hb2 (c_ss hb1)},
	have : ∀y ∈ Y, ∃Z ∈ c, y ∈ Z,
	{
		intros y hy,
		rcases Y_ss hy with ⟨Z, hZc, hyZ⟩,
		exact ⟨Z, hZc, hyZ⟩,
	},
	choose f hfc hf using this,
	have sub_chain_fin := set.finite.dependent_image Y_fin f,
	set sub_chain := {y : set α | ∃ (x : α) (hx : x ∈ Y), y = f x hx}
	with sub_chain_def,
	have sub_chain_ss : sub_chain ⊆ c,
	{
		intros Z hZ,
		rw sub_chain_def at hZ,
		simp at hZ,
		rcases hZ with ⟨y, hyY, hyf⟩,
		rw hyf,
		exact hfc y hyY,
	},
	have Y_nonempty : Y.nonempty,
	{
		rw← set.ne_empty_iff_nonempty,
		intro contra,
		rw contra at hYF,
		exact hYF (mem_empty_of_fin_character ⟨X, hX⟩ F_fin_char),
	},
	have sub_chain_nonempty : sub_chain.nonempty,
	{
		cases Y_nonempty with y hy,
		have : f y hy ∈ sub_chain, {rw sub_chain_def, simp,exact ⟨y, hy, rfl⟩},
		exact set.nonempty_of_mem this,
	},
	rcases max_of_fin_chain sub_chain_fin (is_chain.mono sub_chain_ss c_chain)
	sub_chain_nonempty with ⟨m, hmsub, hm⟩,
	use [m, sub_chain_ss hmsub],
	suffices : Y ⊆ m, {rw F_fin_char, push_neg, exact ⟨Y, this, Y_fin, hYF⟩},
	suffices : ∀y ∈ Y, ∃Z ∈ sub_chain, y ∈ Z,
	{
		intros y hy,
		rcases this y hy with ⟨Z, Z_sub, hyZ⟩,
		exact @hm Z Z_sub y hyZ,
	},

	intros y hy,
	use [f y hy], rw sub_chain_def, simp,
	use [y, hy, rfl, hf y hy],
 end