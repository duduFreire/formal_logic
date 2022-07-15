import tactic 
import order.zorn

variable {α : Type*}

lemma max_of_fin_chain [partial_order α] :
∀{c : set α}, c.finite → is_chain (≤) c → c.nonempty → ∃m ∈ c, ∀{b}, b ∈ c → b ≤ m :=
begin
	intros c c_fin c_chain c_nonempty,
	set P : set α → Prop := λx, (∃(x_fin : x.finite) (x_chain : is_chain (≤) x)
	 (x_nonempty : x.nonempty), true) → ∃m ∈ x, ∀{b}, b ∈ x → b ≤ m with P_def,

	have P_empty : P ∅,
	{
		rw P_def,
		intro h,
		rcases h with ⟨a, a, contra, -⟩, exfalso,
		exact set.not_nonempty_empty contra,
	},

	suffices h : P c, {exact h ⟨c_fin, c_chain, c_nonempty, true.intro⟩},
	apply set.finite.induction_on c_fin P_empty,
	intros a s has s_fin hPs,
	intro h,
	rcases h with ⟨as_finite, as_chain, as_nonemtpty, -⟩,
	have s_chain := is_chain.mono (set.subset_insert a s) as_chain,
	by_cases s_nonempty : s.nonempty,
	{
		rcases hPs ⟨s_fin, s_chain, s_nonempty, true.intro⟩ with ⟨m, hms, hm⟩,
		by_cases h : a ≤ m,
		{
			use [m, set.mem_insert_of_mem a hms],
			intros b hb,
			simp at hb,
			cases hb, {rwa hb},
			{exact hm hb},
		},
		{
			have hmas : m ∈ (insert a s) := set.mem_insert_of_mem a hms,
			have haas : a ∈ (insert a s) := set.mem_insert a s,
			have hma : m ≤ a,
			{
				unfold is_chain at as_chain,
				unfold set.pairwise at as_chain,
				by_cases m_eq_a : m = a, {rw m_eq_a},
				specialize as_chain hmas haas m_eq_a,
				tauto,
			},
			use [a, haas],
			intros b hb, simp at hb,
			cases hb,
			{rw hb},
			{
				specialize hm hb,
				exact le_trans hm hma,
			},
		},
	},
	rw set.not_nonempty_iff_eq_empty at s_nonempty,
	use [a, set.mem_insert a s], rw s_nonempty,
	intros b hb, simp at hb, rw hb,
end

def finite_character (F : set (set α)) : Prop :=
∀ X, X ∈ F ↔ (∀ {Y : set α}, Y ⊆ X → Y.finite → Y ∈ F)

variable {F : set (set α)}

lemma mem_empty_of_fin_character : 
F.nonempty → finite_character F → ∅ ∈ F :=
begin
	intros F_nonempty F_fin_char,
	cases F_nonempty with X hX,
	exact (F_fin_char X).mp hX (set.empty_subset X) set.finite_empty,
end

lemma max_of_fin_character {X} (hX : X ∈ F) :
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
	use [f y hy, y, hy, rfl, hf y hy],
end