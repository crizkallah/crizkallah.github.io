theory Fairness_Fractional_Assignment
  imports 
    Main
    "HOL-Probability.Probability"
    "Randomised_Social_Choice.Randomised_Social_Choice"
    "Randomised_Social_Choice.Utility_Functions"
    "Randomised_Social_Choice.Order_Predicates"
    "Marriage.Marriage"
begin

text\<open>
This is a formalization of some of the results published in the following paper:
  Haris Aziz, Serge Gaspers, Simon Mackenzie, Toby Walsh. 
  Fair assignment of indivisible objects under ordinal preferences.
  Artificial Intelligence (AIJ), 2015.

The formalisation is explained in the following paper:
  Minh Do and Christine Rizkallah. 
  Formalising Fairness in the Assignment Problem with Ordinal Preferences in Isabelle/HOL.
  Conference on Intelligent Computer Mathematics (CICM), 2025.\<close>


(* An assignment is a function, taking an agent as an argument, and outputting the allocation,
which is the fractions/proportions of each alternative assigned to that agent *)
type_synonym 'alt allocation = "'alt \<Rightarrow> real"
type_synonym ('agent, 'alt) assignment = "'agent \<Rightarrow> 'alt allocation"
                                

(* Definition, fractional assignment *)
locale random_allocation = 
  fixes alts :: "'b set"
  fixes h :: "'b allocation"
  assumes finite_alts [simp]: "finite alts"
  assumes undefined_alts [simp]: "j \<notin> alts \<longrightarrow> h j = 0"
  assumes prob [simp]: "\<forall>j \<in> alts. (0 \<le> h j \<and> h j \<le> 1)"


locale random_assignment =
  fixes agents :: "'agent set" and alts :: "'alt set" and R :: "('agent, 'alt) pref_profile"
  assumes "pref_profile_wf agents alts R"
  fixes p :: "('agent, 'alt) assignment"
  assumes random_alloc [simp]: "\<forall>i \<in> agents. random_allocation alts (p i)"
  assumes undefined_agent [simp]: "\<forall>j. i \<notin> agents \<longrightarrow> p i j = 0"
  assumes stochastic [simp]: "\<forall>j \<in> alts. (\<Sum> i\<in>agents. p i j) = 1" 
  assumes sum_prob_equal_agents [simp]: "\<exists>c :: real. \<forall> i \<in> agents. (\<Sum> j \<in> alts. p i j) = c"
  assumes fin [simp]: "finite agents"

definition 
  allocated_alts :: "'alt allocation \<Rightarrow> 'alt set \<Rightarrow> 'alt set"
where
  "allocated_alts p alts = {x. x \<in> alts \<and> p x \<noteq> 0}"

lemma allocated_subset: "\<forall>x :: 'alt set. \<forall>p :: 'alt allocation. allocated_alts p x \<subseteq> x"
  by (simp add: allocated_alts_def)

lemma allocated_ones: "\<forall>x :: 'alt set. \<forall>p :: 'alt allocation. 
  (\<forall>u \<in> x. p u \<noteq> 0 \<longrightarrow> u \<in> allocated_alts p x)"
  by (auto simp add: allocated_alts_def)

definition SDA :: "'alt relation \<Rightarrow> 'alt allocation relation"
  where
  "p \<succeq>[SDA(R)] q \<equiv> \<forall>x. (R x x \<longrightarrow> ((\<Sum>i\<in>{y. R y y \<and> y \<succeq>[R] x}. p i) \<ge> (\<Sum>i\<in>{y. R y y \<and> y \<succeq>[R] x}. q i)))"

lemma SDA_trans: "p \<succeq>[SDA(R)] q \<Longrightarrow> q \<succeq>[SDA(R)] r \<Longrightarrow> p \<succeq>[SDA(R)] r"
  unfolding SDA_def by force

definition sum_utility :: "('a \<Rightarrow> real) \<Rightarrow> 'a set \<Rightarrow> 'a allocation \<Rightarrow> real"
where 
  "sum_utility u A p = (\<Sum>i \<in> A. (u i) * (p i))"

(* Definition, discrete assignment *)
locale discrete_allocation = random_allocation + 
  assumes disc: "\<forall>i \<in> alts. h i = 0 \<or> h i = 1"

sublocale discrete_allocation \<subseteq> random_allocation
  by (simp add: random_allocation_axioms)

context discrete_allocation
begin

lemma sum_ut_eq_sum_alt: "sum_utility u alts h = sum u (allocated_alts h alts)"
proof (unfold sum_utility_def)
  let "?A" = "allocated_alts h alts"
  from disc allocated_alts_def[of "h" "alts"] have "\<forall>x \<in> ?A. h x = 1" by auto
  hence "\<forall>i \<in> ?A. u i * h i = u i" by simp
  from this sum.neutral sum.cong[of "?A" "?A"] have sum_in:"(\<Sum>i \<in> ?A. u i * h i) = (\<Sum>i \<in> ?A. u i)" 
    by meson
  have "(\<Sum>i \<in> ?A. u i) = sum u ?A" by simp
  from this sum_in have sum_in':"(\<Sum>i \<in> ?A. u i * h i) = sum u ?A" by simp
  from disc allocated_alts_def[of "h" "alts"] have "\<forall>x \<in> alts. x \<notin> ?A \<longrightarrow> h x = 0"
    by auto
  hence "\<forall>x \<in> alts - ?A. h x = 0" by simp
  hence "\<forall>i \<in> alts - ?A. u i * h i = 0" by simp
  from this finite_alts have sum_notin: "(\<Sum>i \<in> alts - ?A. u i * h i) = 0" by (meson sum.neutral)
  from finite_alts have "\<forall>x \<in> alts. (x \<in> ?A \<or> x \<in> alts - ?A) \<and> \<not>(x \<in> ?A \<and> x \<in> alts - ?A)" by simp
  from this finite_alts sum.subset_diff allocated_subset 
  have "(\<Sum>i \<in> alts. u i * h i) = (\<Sum>i \<in> ?A. u i * h i) + (\<Sum>i \<in> alts - ?A. u i * h i)" by smt
  from sum_in' sum_notin this show "(\<Sum>i \<in> alts. u i * h i) = sum u ?A" by simp
qed

lemma sum_to_card_allocated: "sum h alts = card (allocated_alts h alts)"
proof -
  from disc have binaries: "\<forall>i \<in> alts. h i = 0 \<or> h i = 1" by auto
  hence "allocated_alts h alts = {x \<in> alts. h x = 1}"
    using allocated_alts_def by fastforce
  have un_alt: "{x \<in> alts. h x = 1} \<union> {x \<in> alts. h x = 0} = alts"
  proof (rule equalityI; rule subsetI)
    show "\<And>x. x \<in> {x \<in> alts. h x = 1} \<union> {x \<in> alts. h x = 0} \<Longrightarrow> x \<in> alts" by force
  next
    fix x
    assume xalts: "x \<in> alts"
    from this binaries have "h x = 0 \<or> h x = 1" by simp
    thus "x \<in> {x \<in> alts. h x = 1} \<union> {x \<in> alts. h x = 0}" 
    proof (cases "h x = 0")
      case True
      from this xalts show ?thesis by simp
    next
      case False
      from this binaries have "h x = 1" by force
      from this xalts show ?thesis by simp
    qed
  qed
  have int_mt: "{x \<in> alts. h x = 1} \<inter> {x \<in> alts. h x = 0} = {}"
  proof (rule equalityI; rule subsetI)
    fix x
    assume intz: "x \<in> {x \<in> alts. h x = 1} \<inter> {x \<in> alts. h x = 0}"
    from this IntD1 have x1:"x \<in> {x \<in> alts. h x = 1}"
      by simp
    from intz IntD2 have x0:"x \<in> {x \<in> alts. h x = 0}"
      by simp
    from x1 x0 have "h x = 1 \<and> h x = 0" by blast
    from this have False by force
    thus "x \<in> {}" by simp
  next
    show "\<And>x. x \<in> {} \<Longrightarrow> x \<in> {x \<in> alts. h x = 1} \<inter> {x \<in> alts. h x = 0}" by (simp add: emptyE)
  qed
  from un_alt int_mt finite_alts sum_Un_eq
  have "sum h {x \<in> alts. h x = 1} + sum h {x \<in> alts. h x = 0} = sum h alts"
    by blast
  moreover have "sum h {x \<in> alts. h x = 0} = 0" by simp
  from binaries have "sum h {x \<in> alts. h x = 1} = card {x \<in> alts. h x = 1}" by simp
(*
  from binaries have "sum h alts = sum h {x \<in> alts. h x = 1} + sum h {x \<in> alts. h x = 0}"
    by (smt (verit) DiffE \<open>allocated_alts h alts = {x \<in> alts. h x = 1}\<close> allocated_subset finite_alts mem_Collect_eq sum.mono_neutral_cong_right sum_nonneg sum_nonpos)
  moreover have "sum h {x \<in> alts. h x = 0} = 0" by auto
  from binaries have "sum h {x \<in> alts. h x = 1} = card {x \<in> alts. h x = 1}" by auto
*)
  moreover from binaries have "{x \<in> alts. h x = 1} = allocated_alts h alts" unfolding allocated_alts_def 
    by auto
  ultimately show "sum h alts = card (allocated_alts h alts)" by auto
qed
end

locale discrete_assignment = random_assignment + 
  assumes discr: 
   "\<forall>i :: 'agent \<in> agent. 
      discrete_allocation alts ((p :: ('agent, 'alt) assignment) i)"

sublocale discrete_assignment \<subseteq> random_assignment
  by (simp add: random_assignment_axioms)

context discrete_assignment
begin
lemma zeros: "\<forall>j \<in> alts. p i j = 0 \<longleftrightarrow> j \<notin> (allocated_alts (p i) alts)"
  by (simp add: allocated_alts_def)

lemma ones: "\<forall>j \<in> alts. p i j = 1 \<longleftrightarrow> j \<in> (allocated_alts (p i) alts)"
  using discr zeros allocated_alts_def discrete_allocation.disc by fastforce
end


section \<open>Responsive set extension\<close>

inductive 
  finite_nonempty :: "'a set \<Rightarrow> bool"  
where
  one: "finite_nonempty {a}" |
  mult: "finite_nonempty A \<Longrightarrow> finite_nonempty (insert a A)"


lemma finite_n_imp_new: 
  "finite_nonempty A \<Longrightarrow>  finite A \<and> A \<noteq> {}"
  by (induct A rule: finite_nonempty.induct) simp+

lemma add_element_nonempt: 
  "finite A \<Longrightarrow> insert a A \<noteq> {}"
  by (induct A rule: finite.induct) simp+

lemma permut_add_set: "insert a (insert b A) = insert b (insert a A)"
  by auto

lemma add_element_nonempt_fin: 
  "finite A \<Longrightarrow> finite_nonempty (insert a A)"
  by (induct A rule: finite.induct) 
     (simp add: one add_element_nonempt permut_add_set mult)+
  
lemma finite_n_imp_old: 
  "\<lbrakk>finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> finite_nonempty A"
  by (induct A rule: finite.induct) 
     (simp add: add_element_nonempt_fin)+
  

lemma equiv_finite: 
  "finite A \<and> A \<noteq> {} \<longleftrightarrow> finite_nonempty A"
  using finite_n_imp_new finite_n_imp_old 
  by blast

lemma card1_fn: 
  "card A \<ge> 1 \<Longrightarrow> finite_nonempty A"
proof -
  assume "card A \<ge> 1"
  hence "A \<noteq> {}" by auto
  from `card A \<ge> 1` have "finite A" 
    using card_eq_0_iff by force
  from `A \<noteq> {}` `finite A` equiv_finite show "finite_nonempty A" by blast
qed

lemma card2_fn: 
  "finite_nonempty A \<Longrightarrow> card A \<ge> 2 \<Longrightarrow> m \<in> A \<Longrightarrow> finite_nonempty (A - {m})"
proof -
  assume "finite_nonempty A"
  assume "card A \<ge> 2"
  assume "m \<in> A"
  hence "card (A - {m}) = card A - 1" by auto
  from this `card A \<ge> 2` have "card (A - {m}) \<ge> 1" by auto
  from this card1_fn show "finite_nonempty (A - {m})" by auto
qed


(* Definition, Responsive Set Extension *)
definition
  RS :: "'alt relation \<Rightarrow> 'alt set relation" 
where
  "p \<succeq>[RS(P)] q \<equiv> 
    \<exists>f :: ('alt \<Rightarrow> 'alt). 
      (inj_on f q  \<and> f ` q \<subseteq> p \<and>
      (\<forall>(x:: 'alt) \<in> q. f x \<succeq>[P] x))"

context pref_profile_wf
begin

(* Lemmas for the properties related to Responsive Set Extension *)
lemma replace_single_opt:
  fixes i :: "'agent"
  assumes i_agent: "i \<in> agents"
  fixes S :: "'alt set"
  assumes alt_set: "S \<subset> alts"
  fixes x y :: "'alt"
  assumes x_in: "x \<in> S"
  assumes y_notin: "y \<notin> S"
  assumes y_alts: "y \<in> alts"
  assumes x_preferred: "x \<succeq>[R i] y"
  shows "S \<succeq>[RS(R i)] insert y (S - {x})"
proof (unfold RS_def)
  define f where "f = (\<lambda>z. if z = y then x else z)"
  have "inj_on f (insert y (S - {x})) \<and> f ` insert y (S - {x}) \<subseteq> S \<and> (\<forall>x\<in>insert y (S - {x}). R i x (f x))" 
  proof (rule conjI)
    let "?T" = "(insert y (S - {x}))"
    show "inj_on f (insert y (S - {x}))"
    proof (unfold inj_on_def, rule ballI, rule ballI, rule impI)
      fix a b
      assume aT: "a \<in> ?T"
      assume bT: "b \<in> ?T"
      assume fab: "f a = f b"
      show "a = b" 
      proof (cases "a = y")
        case True
        from this f_def have "f a = x" by simp
        from this fab have "f b = x" by simp
        {
          assume ny: "b \<noteq> y"
          from this f_def have "f b = b" by simp
          from this fab `f a = x` have "b = x" by simp
          have "x \<notin> ?T" using assms(3) assms(4) by blast
          from this bT `b = x` have False by simp
        }
        hence "b = y" by auto
        from this True show ?thesis by simp
      next
        case False
        from this f_def have "f a = a" by simp
        from this fab have "f b = a" by simp
        {
          assume iy: "b = y"
          from this f_def have "f b = x" by simp
          from this fab `f a = a` have "a = x" by simp
          have "x \<notin> ?T" using assms(3) assms(4) by blast
          from this aT `a = x` have False by simp
        }
        hence "b \<noteq> y" by auto
        from this f_def have "f b = b" by auto
        from this `f a = a` fab show ?thesis by simp
      qed
    qed

    show "f ` insert y (S - {x}) \<subseteq> S \<and> (\<forall>x\<in>insert y (S - {x}). R i x (f x))"
    proof (rule conjI)
      show "f ` insert y (S - {x}) \<subseteq> S" using assms(3) f_def by force
    next
      show "\<forall>x\<in>insert y (S - {x}). R i x (f x)" 
      proof (rule ballI)
        fix m 
        assume mT: "m \<in> ?T"
        show "f m \<succeq>[R i] m"
        proof (cases "m = y")
          case True
          from this f_def have "f m = x" by auto
          from this x_preferred True show ?thesis by simp
        next
          case False
          from this f_def have "f m = m" by auto
          from y_alts alt_set have "?T \<subseteq> alts" by auto
          from this mT have "m \<in> alts" by auto
          from pref_profile_wf_axioms i_agent pref_profile_wf.prefs_wf 
          have "finite_total_preorder_on alts (R i)" 
            by simp
          from this finite_total_preorder_on_def 
          have "total_preorder_on alts (R i)" 
            by auto
          from this total_preorder_on.total `m \<in> alts`
          have "(R i) m m \<or> (R i) m m" 
            by force
          hence "m \<succeq>[R i] m" by auto
          from this `f m = m` show ?thesis by auto
        qed
      qed
    qed
  qed
  from this 
  show "\<exists>f. inj_on f (insert y (S - {x})) \<and> 
            f ` insert y (S - {x}) \<subseteq> S \<and> 
            (\<forall>x\<in>insert y (S - {x}). R i x (f x))" 
    by auto
qed


lemma remove_single_opt:
  fixes i :: "'agent"
  assumes i_agent: "i \<in> agents"
  fixes S :: "'alt set"
  assumes alt_set: "S \<subset> alts"
  fixes x :: "'alt"
  assumes x_in: "x \<in> S"
  shows "S \<succ>[RS(R i)] S - {x}"
unfolding strongly_preferred_def
proof (rule conjI)
  let "?T" = "S - {x}"
  have "?T \<subseteq> S" by auto
  show "S \<succeq>[RS(R i)] ?T"
  proof (unfold RS_def)
    define f :: "'alt \<Rightarrow> 'alt" where "f = (\<lambda>x. x)"
    have "inj_on f ?T \<and> f ` ?T \<subseteq> S \<and> (\<forall>x\<in>?T. R i x (f x))" 
    proof (rule conjI)
      show "inj_on f ?T"
      proof (unfold inj_on_def, rule ballI, rule ballI, rule impI)
        fix a b
        assume asx: "a \<in> ?T"
        assume bsx: "b \<in> ?T"
        assume eqab: "f a = f b"
        from f_def have "f a = a" and "f b = b" by auto
        from this eqab show "a = b" by presburger
      qed
    next
      show "f ` (S - {x}) \<subseteq> S \<and> (\<forall>x\<in>S - {x}. R i x (f x))"
      proof (rule conjI, unfold subset_eq, rule ballI)
        fix x
        assume xim: "x \<in> f ` ?T"
        with image_def have "\<exists>u \<in> ?T. x = f u" 
          by auto
        then obtain u where "u \<in> ?T \<and> x = f u" 
          by auto
        hence "f u = x" and "u \<in> ?T"  
          by auto
        from f_def have "f u = u" 
          by simp
        from this `f u = x` have "x = u" 
          by simp
        from this `u \<in> ?T` have "x \<in> ?T" 
          by simp
        moreover with `?T \<subseteq> S` show "x \<in> S" 
          by auto
      next
        show "\<forall>x\<in>S - {x}. R i x (f x)"
        proof (rule ballI)
          fix x
          assume xs: "x \<in> ?T"
          from prefs_wf pref_profile_wf_axioms i_agent 
          have fn: "finite_total_preorder_on alts (R i)" by auto
          from f_def have "f x = x" by simp
          from xs have "x \<in> S" by auto
          from alt_set this have "x \<in> alts" by auto
          from fn finite_total_preorder_on_def have "total_preorder_on alts (R i)" by auto
          from this `x \<in> alts` total_preorder_on.total have "(R i) x x \<or> (R i) x x" by force
          hence "x \<succeq>[R i] x" by auto
          from this `f x = x` show "f x \<succeq>[R i] x" by simp
      qed
    qed
  qed
  thus "\<exists>f. inj_on f (S - {x}) \<and> f ` (S - {x}) \<subseteq> S \<and> (\<forall>x\<in>S - {x}. R i x (f x))" 
    by auto
  qed
  show "\<not> RS (R i) S (S - {x})"
  proof (unfold RS_def, rule notI)
    assume f_ex: "\<exists>f. inj_on f S \<and> f ` S \<subseteq> S - {x} \<and> (\<forall>x\<in>S. R i x (f x))"
    from this obtain f where f_cond: "inj_on f S \<and> f ` S \<subseteq> S - {x} \<and> (\<forall>x\<in>S. R i x (f x))" by auto
    hence inj_f: "inj_on f S" and im_f: "f ` S \<subseteq> ?T" and pref: "\<forall>x \<in> S. f x \<succeq>[R i] x" 
      by auto
    from inj_f have fless: "card S \<le> card (f ` S)" by (simp add: card_image)
    from prefs_wf pref_profile_wf_axioms i_agent 
    have fn: "finite_total_preorder_on alts (R i)" by auto
    hence "finite alts" by simp
    with alt_set have "finite S" 
      using finite_subset by blast
    from im_f this have "card (f ` S) \<le> card ?T" 
      by (simp add: card_mono)
    from fless this have sleqt: "card S \<le> card ?T" 
      by simp
    from  `finite S` x_in card_Diff1_less 
    have sget: "card ?T < card S" 
      by fast
    from sleqt sget show False 
      by simp
  qed
qed
end


definition total_transitive_on :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where 
"total_transitive_on R S \<equiv> 
    ((\<forall>x\<in> S. \<forall>y \<in> S. R x y \<or> R y x) \<and>
    (\<forall>x \<in> S. \<forall>y \<in> S. \<forall>z \<in> S. R x y \<and> R y z \<longrightarrow> R x z))"

lemma total_transitive_on_subset: 
  "total_transitive_on R S \<Longrightarrow> S' \<subseteq> S \<Longrightarrow> total_transitive_on R S'"
unfolding total_transitive_on_def
proof -
  assume ori: "(\<forall>x\<in>S. \<forall>y\<in>S. R x y \<or> R y x) \<and> (\<forall>x\<in>S. \<forall>y\<in>S. \<forall>z\<in>S. R x y \<and> R y z \<longrightarrow> R x z)"
  assume subs: "S' \<subseteq> S"
  show "(\<forall>x\<in>S'. \<forall>y\<in>S'. R x y \<or> R y x) \<and> (\<forall>x\<in>S'. \<forall>y\<in>S'. \<forall>z\<in>S'. R x y \<and> R y z \<longrightarrow> R x z)"
  proof (rule conjI, rule ballI, rule ballI)
    fix x y
    assume xs': "x \<in> S'"
    assume ys': "y \<in> S'"
    from xs' ys' subs have xs: "x \<in> S" and ys: "y \<in> S" by auto
    from ori xs ys show "R x y \<or> R y x" by blast
  next 
    show "\<forall>x\<in>S'. \<forall>y\<in>S'. \<forall>z\<in>S'. R x y \<and> R y z \<longrightarrow> R x z"
    proof (rule ballI, rule ballI, rule ballI)
      fix x y z
      assume xs': "x \<in> S'"
      assume ys': "y \<in> S'"
      assume zs': "z \<in> S'"
      from xs' ys' zs' subs have xs: "x \<in> S" and ys: "y \<in> S" and zs: "z \<in> S" by auto
      from ori xs ys zs show "R x y \<and> R y z \<longrightarrow> R x z" by blast
    qed
  qed
qed

lemma exist_minimal_element: 
  "finite_nonempty S \<Longrightarrow> total_transitive_on R S \<Longrightarrow> (\<exists>x \<in> S. \<forall>y \<in> S. R x y)"
proof (induction S rule: finite_nonempty.induct)
  case (one a)
  thus ?case
  proof (unfold total_transitive_on_def)
    assume total_trans: "(\<forall>x\<in>{a}. \<forall>y\<in>{a}. R x y \<or> R y x) \<and> 
                  (\<forall>x\<in>{a}. \<forall>y\<in>{a}. \<forall>z\<in>{a}. R x y \<and> R y z \<longrightarrow> R x z)"
    hence total: "\<forall>x\<in>{a}. \<forall>y\<in>{a}. R x y \<or> R y x" and 
                   trans: "\<forall>x\<in>{a}. \<forall>y\<in>{a}. \<forall>z\<in>{a}. R x y \<and> R y z \<longrightarrow> R x z" by auto
    show "\<exists>x\<in>{a}. \<forall>a\<in>{a}. R x a"
    proof (rule bexI)
      from total have "\<forall>x \<in> {a}. R x x" by auto
      hence "R a a" by simp
      thus "\<forall>x \<in> {a}. R a x" by blast
      show "a \<in> {a}" by simp
    qed
  qed
next
  case (mult A a)
  have "A \<subseteq> insert a A" by auto
  from `total_transitive_on R (insert a A)` this have reduced_t_t: "total_transitive_on R A" 
    by (simp add: total_transitive_on_subset)
  assume fa: "finite_nonempty A"
  assume "total_transitive_on R A \<Longrightarrow> \<exists>x\<in>A. Ball A (R x)"
  assume ttransE: "total_transitive_on R (insert a A)"
  from reduced_t_t `total_transitive_on R A \<Longrightarrow> \<exists>x\<in>A. \<forall>a\<in>A. R x a` have exMin: "\<exists>x\<in>A. \<forall>a\<in>A. R x a" 
    by simp
  from exMin obtain m where minM: "m \<in> A \<and> (\<forall>a \<in> A. R m a)" by blast
  let "?E" = "insert a A"
  show "\<exists>x\<in>insert a A. Ball (insert a A) (R x)"
  proof (cases "R m a")
    case True
    thus ?thesis
    proof -
      from True minM have "\<forall>x \<in> insert a A. R m x" by simp
      from this minM show "\<exists>m \<in> insert a A. \<forall>x \<in> insert a A. R m x" by auto
    qed
  next
    case False
    from minM have least: "\<forall>a \<in> A. R m a" by simp
    from minM have inA: "m \<in> A" by simp
    hence mE: "m \<in> ?E" by simp
    have aE: "a \<in> ?E" by simp
    from `total_transitive_on R (insert a A)` have tot: "\<forall>x \<in> ?E. \<forall>y \<in> ?E. R x y \<or> R y x" 
      unfolding total_transitive_on_def by blast
    hence "R m a \<or> R a m" using  mE aE by (simp add: tot)
    with False have ram: "R a m" by simp
    have "\<forall>x \<in> ?E. R a x" 
      by (metis aE insertE least mE mult.prems ram total_transitive_on_def)
    thus "\<exists>m \<in> insert a A. \<forall>x \<in> insert a A. R m x" 
      by auto
  qed
qed

lemma exists_ordered_seq: 
  "finite_nonempty A \<Longrightarrow> total_transitive_on Rel A \<Longrightarrow> 
      \<exists>a :: nat \<Rightarrow> 'a. 
        (\<forall>i j. (1 \<le> i \<and> i \<le> card A \<and> 1 \<le> j \<and> j \<le> card A \<longrightarrow> (i < j \<longrightarrow> a j \<succeq>[Rel] a i))) \<and> 
        (\<forall>i. 1 \<le> i \<and> i \<le> card A \<longrightarrow> a i \<in> A) \<and> 
        inj_on a {1::nat..card A}"
proof (induction "card A" arbitrary: A)
  case 0
  thus ?case by auto
next
  case (Suc x)
  thus ?case
  proof (cases "x = 0")
    case True
    hence "Suc x = 1" by simp
    from `Suc x = card A` this have "card A = 1" by simp
    hence "\<exists>a. A = {a}" by (simp add: card_1_singleton_iff)
    from this obtain a where "A = {a}" by auto
    define u :: "nat \<Rightarrow> 'a" where "u = (\<lambda>x. (if x = 1 then a else undefined))" 
    hence u_prop: " (\<forall>i j. (1 \<le> i \<and> i \<le> card A \<and> 1 \<le> j \<and> j \<le> card A \<and> i < j \<longrightarrow> u j \<succeq>[Rel] u i)) 
      \<and> (\<forall>i. 1 \<le> i \<and> i \<le> card A \<longrightarrow> u i \<in> A)" using \<open>A = {a}\<close> by auto
    from u_def have  "inj_on u {1}" by blast
    hence inj: "inj_on u {1..1}" by auto
    from u_def have "u 0 = undefined" by auto
    from this u_prop inj `card A = 1` show ?thesis by auto
  next
    case False
    from `finite_nonempty A` `total_transitive_on Rel A` exist_minimal_element[of "A" "Rel"] 
    have "\<exists>x \<in> A. \<forall>y \<in> A. y \<succeq>[Rel] x" by simp
    from this obtain m where m_prop: "m \<in> A \<and> (\<forall>y \<in> A. y \<succeq>[Rel] m)" by auto
    let "?a" = "A - {m}"
    from `Suc x = card A` have card_prem:"x = card ?a" by (simp add: m_prop)
    from this `Suc x = card A` have diff_card: "card ?a = card A - 1" by simp
    from `finite_nonempty A` have fn_prem: "finite_nonempty ?a"
      by (metis False \<open>x = card (A - {m})\<close> card_eq_0_iff finite_n_imp_old)
    have subz: "?a \<subseteq> A" by auto
    from `total_transitive_on Rel A` subz have ttrans_prem: "total_transitive_on Rel ?a" 
      by (smt (verit, ccfv_threshold) Set.basic_monos(7) total_transitive_on_def)
    from card_prem fn_prem ttrans_prem Suc(1)[of "?a"] 
    have "\<exists>a. (\<forall>i j. (1 \<le> i \<and> i \<le> card ?a \<and> 1 \<le> j \<and> j \<le> card ?a \<longrightarrow> i < j \<longrightarrow> Rel (a i) (a j))) \<and>
              (\<forall>i. 1 \<le> i \<and> i \<le> card ?a \<longrightarrow> a i \<in> ?a) \<and> 
              inj_on a {1..card ?a}" by auto
    from this obtain a_x where a_x_prop: "(\<forall>i j. (1 \<le> i \<and> i \<le> card ?a \<and> 1 \<le> j \<and> j \<le> card ?a \<longrightarrow>
         i < j \<longrightarrow> Rel (a_x i) (a_x j))) \<and> 
      (\<forall>i. 1 \<le> i \<and> i \<le> card ?a \<longrightarrow> a_x i \<in> ?a) \<and> inj_on a_x {1..card ?a}" by auto
    define a_sx :: "nat \<Rightarrow> 'a" where "a_sx = (\<lambda>x. if x = 1 then m else a_x (x - 1))"
    have "(\<forall>i j. 1 \<le> i \<and> i \<le> card A \<and> 1 \<le> j \<and> j \<le> card A \<longrightarrow> ( i < j \<longrightarrow> Rel (a_sx i) (a_sx j))) \<and> 
    (\<forall>i. 1 \<le> i \<and> i \<le> card A \<longrightarrow> a_sx i \<in> A) \<and> inj_on a_sx {1..card A}"
    proof (rule conjI, rule allI, rule allI, rule impI)
      fix i j
      assume range_ij: "1 \<le> i \<and> i \<le> card A \<and> 1 \<le> j \<and> j \<le> card A"
      show "i < j \<longrightarrow> Rel (a_sx i) (a_sx j)"
      proof (rule impI)
        assume lij: "i < j"
        show "Rel (a_sx i) (a_sx j)"
        proof (cases "i = 1")
          case True
          from lij have "i < j" by auto
          from range_ij have " 1 \<le> j \<and> j \<le> card A" by auto
          from this `i < j` local.True have range_j: "2 \<le> j \<and> j \<le> card A" by auto
          from local.True a_sx_def have "a_sx i = m" by simp
          from range_j have "j \<noteq> 1" by auto
          from this a_sx_def have "a_sx j = a_x (j - 1)" by force
          from a_x_prop have "\<forall>i. 1 \<le> i \<and> i \<le> card (A - {m}) \<longrightarrow> a_x i \<in> A - {m}" by auto
          from this diff_card have inele: "\<forall>i. 1 \<le> i \<and> i \<le> card A - 1 \<longrightarrow> a_x i \<in> A - {m}" by simp
          from range_j have "1 \<le> j - 1 \<and> j - 1 \<le> card A - 1" by auto
          from this inele have "a_x (j - 1) \<in> ?a" by simp
          from this `a_sx j = a_x (j - 1)` have "a_sx j \<in> ?a" by auto
          hence "a_sx j \<in> A" by auto
          from m_prop have "\<forall>y \<in> A. y \<succeq>[Rel] m" by auto
          from this `a_sx j \<in> A`  `a_sx i = m` show "a_sx j \<succeq>[Rel] a_sx i" by auto
        next
          case False
          from range_ij have "1 \<le> i \<and> i \<le> card A" by simp
          from this False have range_i: "2 \<le> i \<and> i \<le> card A" by simp
          from range_ij have "1 \<le> j \<and> j \<le> card A" by simp
          from this lij range_i have range_j: "3 \<le> j \<and> j \<le> card A" by auto
          from range_j have "j \<noteq> 1" by auto
          from this a_sx_def have sxj: "a_sx j = a_x (j - 1)" by simp
          from range_i have "i \<noteq> 1" by auto
          from this a_sx_def have sxi: "a_sx i = a_x (i - 1)" by simp
          from range_j have ir: "1 \<le> j - 1 \<and> j - 1 \<le> card A - 1" by auto
          from range_i have jr: "1 \<le> i - 1 \<and> i - 1 \<le> card A - 1" by auto
          from lij have "(i - 1) < (j - 1)"
            using less_diff_iff range_ij by presburger
          from this jr ir a_x_prop have "a_x (j - 1) \<succeq>[Rel] a_x (i - 1)"
            using diff_card by presburger
          from this sxi sxj show "a_sx j \<succeq>[Rel] a_sx i" by simp
        qed
      qed
    next
      show "(\<forall>i. 1 \<le> i \<and> i \<le> card A \<longrightarrow> a_sx i \<in> A) \<and> inj_on a_sx {1..card A}"
      proof (rule conjI, rule allI, rule impI)
        fix i
        assume range_i: "1 \<le> i \<and> i \<le> card A"
        show "a_sx i \<in> A"
        proof (cases "i = 1")
          case True
          from True a_sx_def have "a_sx i = m" by simp
          from m_prop have "m \<in> A" by simp
          from this `a_sx i = m` show "a_sx i \<in> A" by simp
        next
          case False
          from False a_sx_def have eq_sx: "a_sx i = a_x (i - 1)" by simp
          from False range_i have "2 \<le> i \<and> i \<le> card A" by arith
          hence "1 \<le> i - 1 \<and> i - 1 \<le> card A - 1" by arith
          from this diff_card have "1 \<le> i - 1 \<and> i - 1 \<le> card ?a" by simp
          from a_x_prop this have "a_x (i - 1) \<in> ?a" by simp
          from this eq_sx have "a_sx i \<in> ?a" by simp
          thus "a_sx i \<in> A" by auto
        qed
      next
        show "inj_on a_sx {1..card A}"
        proof (unfold inj_on_def, rule ballI, rule ballI, rule impI)
          fix x y
          assume xa: "x \<in> {1..card A}"
          assume ya: "y \<in> {1..card A}"
          assume asx_eq: "a_sx x = a_sx y"
          have m_not: "m \<notin> ?a" by auto
          show "x = y"
          proof (cases "x = 1")
            case True
            from True a_sx_def have "a_sx x = m" by simp
            from this asx_eq have "a_sx y = m" by simp
            have "y = 1"
            proof (rule ccontr)
              assume n1: "y \<noteq> 1"
              from this a_sx_def have "a_sx y = a_x (y - 1)" by simp
              from ya n1 have "2 \<le> y \<and> y \<le> card A" by simp
              hence "1 \<le> y - 1 \<and> y - 1 \<le> card A - 1" by arith
              from this a_x_prop diff_card have "a_x (y - 1) \<in> ?a" by simp
              from this `a_sx y = a_x (y - 1)` have "a_sx y \<in> ?a" by simp
              from this `a_sx y = m` show False by auto
            qed
            from this True show ?thesis by arith
          next
            case False
            from this a_sx_def have "a_sx x = a_x (x - 1)" by simp
            from xa False have "2 \<le> x \<and> x \<le> card A" by simp
            hence rx: "1 \<le> x - 1 \<and> x - 1 \<le> card A - 1" by arith
            from this diff_card have xin: "x - 1 \<in> {1..card ?a}" by simp
            from rx a_x_prop diff_card have "a_x (x - 1) \<in> ?a" by simp
            from this `a_sx x = a_x (x - 1)` have a_sx_elem:"a_sx x \<in> ?a" by auto
            then have n1: "y \<noteq> 1" 
              using a_sx_def asx_eq by force
            from this a_sx_def have "a_sx y = a_x (y - 1)" by simp
            from ya n1 have "2 \<le> y \<and> y \<le> card A" by simp
            hence ry: "1 \<le> y - 1 \<and> y - 1 \<le> card A - 1" by arith
            from this diff_card have yin: "y - 1 \<in> {1..card ?a}" by simp
            from asx_eq `a_sx x = a_x (x - 1)` `a_sx y = a_x (y - 1)` 
            have "a_x (x - 1) = a_x (y - 1)" by simp
            from a_x_prop have "inj_on a_x {1..card ?a}" by simp
            from this xin yin `a_x (x - 1) = a_x (y - 1)` have "x - 1 = y - 1" 
              unfolding inj_on_def by blast
            thus "x = y" using ry by linarith
          qed
        qed
      qed
    qed
    thus ?thesis by auto
  qed
qed

lemma empty_range: "(j::nat) < i \<Longrightarrow> {i..j} = {}"
  by simp

lemma alternating_sum: 
  assumes "(i::nat) < j"
  shows "(\<Sum>(k::nat) \<in> {i..j}. (f :: (nat \<Rightarrow> real)) k - f (k-1)) = f j - f (i-1)"
using assms
proof (induction "j - i" arbitrary: j i)
  case 0
  from 0(1) 0(2) have False by simp
  thus ?case by auto
next
  case (Suc x)
  thus ?case 
  proof (cases "x = 0")
    case True
    hence "Suc x = 1" by auto
    from this Suc(2) have "j - i = 1" by auto
    hence "{i..j} = {i,j}" by auto
    from this `j-i = 1` have sumsimp: "(\<Sum>k = i..j. f k - f (k - 1)) = f j - f (j-1) + f i - f (i-1)" by simp
    from `j - i = 1` have "j - 1 = i" by auto
    hence "f (j-1) = f i" by auto
    hence "f j - f (j-1) + f i - f (i-1) = f j - f (i-1)" by auto
    from this sumsimp show ?thesis by auto
  next
    case False
    hence "x > 0" by auto
    from Suc(2) have "x = j - i - 1" by auto
    hence xp: "x = (j-1) - i" by auto
    from this `x > 0` have "j-1 > i" by auto
    from this Suc(1) xp have ih: "(\<Sum>k = i..j-1. f k - f (k - 1)) = f (j-1) - f (i - 1)" by auto
    have "j = Suc (j-1)" using Suc.prems by force
    hence "(\<Sum>k \<in> {i..j}. f k - f (k - 1)) = 
      (\<Sum>k \<in> {i..j-1}. f k - f (k - 1)) + f j - f (j-1)" 
      by (metis (no_types, lifting) Suc(3) add.commute diff_add_eq 
          less_SucI linorder_not_less not_less_eq sum.nat_ivl_Suc')
    from ih this have "(\<Sum>k \<in> {i..j}. f k - f (k - 1)) = f (j-1) - f (i - 1) + f j - f (j-1)"
      by auto
    thus "(\<Sum>k \<in> {i..j}. f k - f (k - 1)) = f j - f (i - 1)" by auto
  qed
qed


lemma abel_summation: 
  assumes"(n::nat) \<ge> 1" 
  shows "\<And>f g:: (nat \<Rightarrow> real). 
    (\<Sum>i \<in> {1..n}. f i * g i) = 
    f 1 * (\<Sum>k \<in> {1..n}. g k) + 
      (\<Sum>j \<in> {2::nat..n}. (f j - f (j-1)) * (\<Sum>k \<in> {j..n}. g k))" 
using assms
proof (induct n)
  case 0
  hence False by force
  thus ?case by simp
next
  case (Suc n)
  thus ?case 
  proof (cases n)
    case (Suc nat)
    hence IH: "(\<Sum>i = 1..n. f i * g i) =
                   f 1 * sum g {1..n} + (\<Sum>j = 2..n. (f j - f (j - 1)) * sum g {j..n})"
      using Suc.hyps by simp 
    let "?m" = "Suc n"
    have "\<forall>j \<in> {2::nat..?m}. (f j - f (j-1)) * (\<Sum>k \<in> {j..?m}. g k) = 
         (f j - f (j-1)) * (\<Sum>k \<in> {j..n}. g k) + (f j - f (j-1)) * g ?m"
      by (simp add: cross3_simps(24))
    then have 
      "(\<Sum>j \<in> {2::nat..?m}. (f j - f (j-1)) * (\<Sum>k \<in> {j..?m}. g k)) =
       (\<Sum>j = 2..?m. ((f j - f (j - 1)) * sum g {j..n}) + ((f j - f (j - 1)) * g ?m))" 
      by auto
    moreover 
    have "(\<Sum>j = 2..?m. ((f j - f (j - 1)) * sum g {j..n}) + ((f j - f (j - 1)) * g ?m)) =
    (\<Sum>j = 2..?m. ((f j - f (j - 1)) * sum g {j..n})) + (\<Sum>j = 2..?m. (f j - f (j - 1)) * g ?m)"
      by (simp add: sum.distrib)
    moreover 
    have "f 1 * g ?m + (\<Sum>j = 2..?m. (f j - f (j - 1)) * g ?m) = f ?m * g ?m"
    proof (cases "?m = 2")
      case True 
      hence "{2..?m} = {?m}" by auto
      hence "(\<Sum>j = 2..?m. (f j - f (j - 1)) * g ?m) = (f ?m - f (?m - 1)) * g ?m" 
        by auto
      moreover 
      have "(f ?m - f (?m - 1)) * g ?m = f ?m * g ?m - f (?m - 1) * g ?m" 
        by argo
      moreover 
      have "?m - 1 = 1" by (simp add: True)
      ultimately 
      have "(\<Sum>j = 2..?m. (f j - f (j - 1)) * g ?m) = f ?m * g ?m - f 1 * g ?m" by auto
      thus ?thesis 
        by auto
    next
      case False
      hence gr_2: "?m > 2"
        by (simp add: Suc)
      have distr: 
        "(\<Sum>j = 2..?m. (f j - f (j - 1)) * g ?m) = (\<Sum>j = 2..?m. f j - f (j - 1)) * g ?m"
        by (metis (no_types) sum_distrib_right)
      have "(\<Sum>j = 2..?m. f j - f (j - 1)) = f ?m - f ((2::nat) - 1)"
        using gr_2 alternating_sum by blast
      hence "(\<Sum>j = 2..?m. f j - f (j - 1)) = f ?m - f 1"
        by simp 
      with distr 
      have "(\<Sum>j = 2..?m. (f j - f (j - 1)) * g ?m) = (f ?m - f 1) * g ?m" 
        by auto
      moreover 
      have "(f ?m - f 1) * g ?m = f ?m * g ?m - f 1 * g ?m" 
        by argo
      ultimately 
      show ?thesis 
        by argo
    qed
    moreover 
    have "f 1 * sum g {1..?m} = f 1 * sum g {1..n} + f 1 * g ?m" 
      by (simp add: cross3_simps(24))
    ultimately
    have "f 1 * sum g {1..Suc n} + (\<Sum>j = 2..Suc n. (f j - f (j - 1)) * sum g {j..Suc n}) = 
          f 1 * sum g {1..n} + (\<Sum>j = 2..Suc n. (f j - f (j - 1)) * sum g {j..n}) + 
          f (Suc n) * g (Suc n)" 
      by linarith
    with IH have 
      "f 1 * sum g {1..Suc n} + (\<Sum>j = 2..Suc n. (f j - f (j - 1)) * sum g {j..Suc n}) = 
      (\<Sum>i = 1..n. f i * g i) + f ?m * g ?m" 
      by simp
    thus ?thesis 
      by simp
  qed (simp)
qed


lemma first_order_nonneg: "\<forall>\<epsilon>::real > 0. (a::real) +  \<epsilon> * (b::real) \<ge> 0 \<Longrightarrow> a \<ge> 0"
proof -
  assume all_e_sm: "\<forall>\<epsilon>>0. 0 \<le> a + \<epsilon> * b"
  have "b \<ge> 0"
  proof (rule ccontr)
    assume b_nge_0: "\<not> 0 \<le> b"
    thus False
    proof (cases "a > 0")
      case True
      hence "a + (-2*a / b) * b < 0"
        using b_nge_0 by force
      moreover from True b_nge_0 have "-2 * a / b > 0" 
        using zero_less_divide_iff by fastforce
      ultimately have "\<exists>\<epsilon> > 0. a + \<epsilon> * b < 0" by fast
      thus False 
        using all_e_sm by fastforce
    next
      case False
      have "(1::real) > 0" by auto
      with all_e_sm  
      have "a + b * (1::real) \<ge> 0"
        by (metis mult.commute)
      thus False 
        using False b_nge_0 by linarith
    qed
  qed
  show "a \<ge> 0"
  proof (cases "b = 0")
    case True
    from True have "\<forall>\<epsilon>. a + \<epsilon> * b = a" by simp
    from this all_e_sm have "\<forall>\<epsilon>>0. a \<ge> 0" 
      by (metis gt_ex)
    thus "a \<ge> 0" by auto
  next
    case False
    show ?thesis 
    proof (rule ccontr)
      assume "\<not> 0 \<le> a"
      hence "a/2 < 0" and "-a > 0" by simp+
      have "(-a / b) * b = -a" 
        using False by simp
      hence "(-a / (2 * b)) * b = -a / 2" 
        by linarith 
      hence "a + (-a / (2 * b)) * b = a / 2"
        by (simp add: False)
      with `a/2 < 0` have "a + (-a / (2 * b)) * b < 0" 
        by auto
      have "b > 0" 
        using  False `b \<ge>0`  by simp
      hence "-a / (2 * b) > 0"
        using divide_pos_pos `-a > 0` by fastforce
      hence "\<exists>\<epsilon>>0. a + \<epsilon> * b < 0"
        using `a + (-a / (2 * b)) * b < 0` by blast
      thus False 
        using all_e_sm by force 
    qed
  qed
qed




locale random_pair_allocation = 
  fixes alts :: "'alt set"
  fixes p q :: "'alt allocation"
  fixes R :: "'alt relation"
  assumes nonempty_a: "alts \<noteq> {}"
  assumes alts_rel: "finite_total_preorder_on alts R"
  assumes ra_p: "random_allocation alts p"
  assumes ra_q: "random_allocation alts q"
  assumes sum_prob: "(\<Sum>i \<in> alts. p i) = (\<Sum>i \<in> alts. q i)"
begin

lemma card_sub_alts:  
  "x \<in> alts \<Longrightarrow> {t. R t t \<and> R t x} \<subseteq> alts"
  by (metis (mono_tags, lifting) finite_total_preorder_on_def mem_Collect_eq 
      alts_rel preorder_on.not_outside(2) subset_eq total_preorder_on_def)

lemma card_less_set:
  "x \<preceq>[R] y \<Longrightarrow> {t. R t t \<and> R t x} \<subseteq> {t. R t t \<and> R t y}"
proof (rule subsetI)
  fix u
  assume ord_xy: "R x y"
  assume "u \<in> {t. R t t \<and> R t x}"
  hence "R u u" and "R u x" by auto
  from `R u x` `R x y` have "R u y" 
    by (meson alts_rel finite_total_preorder_on.axioms(1) preorder_on.trans total_preorder_on.axioms(1))
  from `R u u` this
  show "u \<in> {t. R t t \<and> R t y}" by auto
qed

lemma card_impl_rel:
  fixes x y
  assumes x_in_alts: "x \<in> alts"
  assumes y_in_alts: "y \<in> alts" 
  assumes tset:"{t. R t t \<and> R t x} \<subseteq> {t. R t t \<and> R t y}"
  shows "x \<preceq>[R] y"
  using assms
proof -
  have "\<forall>t. R t t \<and> R t x \<longrightarrow> R t y" 
    using tset by auto
  hence t_item: "\<forall>t \<in> alts. R t x \<longrightarrow> R t y" 
    by (metis alts_rel finite_total_preorder_on_iff total_preorder_on.total)
  have "R x x" 
    by (metis alts_rel finite_total_preorder_on_iff total_preorder_on.total x_in_alts)
  with x_in_alts t_item 
  show "R x y" by auto
qed

lemma not_rel_card_subless: 
  fixes x y
  assumes "x \<prec>[R] y"
  shows "{t. R t t \<and> R t x} \<subset> {t. R t t \<and> R t y}" 
  using assms
proof -
  from assms have "x \<preceq>[R] y" using strongly_preferred_def[of "x" "R" "y"] 
    by auto
  with card_less_set have "{t. R t t \<and> R t x} \<subseteq> {t. R t t \<and> R t y}" 
    by auto
  moreover
  have "{t. R t t \<and> R t x} \<noteq> {t. R t t \<and> R t y}"
  proof (rule ccontr)
    assume "\<not> {t. R t t \<and> R t x} \<noteq> {t. R t t \<and> R t y}"
    hence "{t. R t t \<and> R t x} = {t. R t t \<and> R t y}" 
      by auto
    hence "{t. R t t \<and> R t y} \<subseteq> {t. R t t \<and> R t x}" 
      by auto
    hence "R y x"
      using \<open>R x y\<close> card_impl_rel alts_rel finite_total_preorder_on.axioms(1) 
            preorder_on.not_outside(2) total_preorder_on.axioms(1) 
      by fastforce
    thus False using assms strongly_preferred_def[of x R y] by auto
  qed
  ultimately 
  show "{t. R t t \<and> R t x} \<subset> {t. R t t \<and> R t y}" 
    by auto
qed

lemma card_utility_func: 
  "vnm_utility alts R (\<lambda>x. card {y. R y y \<and> R y x})"
unfolding vnm_utility_def vnm_utility_axioms_def
proof (rule conjI)
  from alts_rel show "finite_total_preorder_on alts R" by auto
  let "?f" = "(\<lambda>x. card {y. R y y \<and> R y x})"
  let "?S" = "\<lambda>x. {y. R y y \<and> R y x}"
  show "\<forall>x y. x \<in> alts \<longrightarrow> y \<in> alts \<longrightarrow> 
          (real (card {y. R y y \<and> R y x}) \<le> real (card {ya. R ya ya \<and> R ya y})) = R x y"
  proof (rule allI, rule allI, rule impI, rule impI)
    fix x y
    assume xa: "x \<in> alts"
    assume ya: "y \<in> alts"
    from xa ya have totalthis: "R x y \<or> R y x"
      by (metis alts_rel finite_total_preorder_on_def total_preorder_on.total)
    from this card_less_set have or_subset: "{t. R t t \<and> R t x} \<subseteq> {t. R t t \<and> R t y} \<or>
    {t. R t t \<and> R t y} \<subseteq> {t. R t t \<and> R t x}" by auto

    show "real (?f x) \<le> real (?f y) =  R x y"
    proof (rule iffI)
      assume "real (?f x) \<le> real (?f y)"
      hence cardxles: "card {t. R t t \<and> R t x} \<le> card {t. R t t \<and> R t y}" by auto
      have "{t. R t t \<and> R t x} \<subseteq> {t. R t t \<and> R t y}" 
      proof (rule ccontr)
        assume asmp: "\<not> {t. R t t \<and> R t x} \<subseteq> {t. R t t \<and> R t y}"
        from this or_subset have ysubx:"{t. R t t \<and> R t y} \<subseteq> {t. R t t \<and> R t x}" by auto
        from xa ya this card_sub_alts have "card {t. R t t \<and> R t y} \<le> card {t. R t t \<and> R t x}"
          by (meson alts_rel card_mono finite_total_preorder_on_iff rev_finite_subset)
        from this cardxles have "card {t. R t t \<and> R t x} = card {t. R t t \<and> R t y}" by auto
        from this ysubx card_sub_alts have "{t. R t t \<and> R t y} = {t. R t t \<and> R t x}"
          by (metis alts_rel card_subset_eq finite_subset finite_total_preorder_on.finite_carrier xa)
        hence "{t. R t t \<and> R t x} \<subseteq> {t. R t t \<and> R t y}" by auto
        from this asmp show False by auto
      qed
      from xa ya this card_impl_rel show "R x y" by auto
    next
      assume "R x y"
      from this card_less_set have "{t. R t t \<and> R t x} \<subseteq> {t. R t t \<and> R t y}" by auto
      from this card_sub_alts have "card {t. R t t \<and> R t x} \<le> card {t. R t t \<and> R t y}" 
        by (meson alts_rel card_mono finite_total_preorder_on_iff rev_finite_subset ya)
      thus "real (card {t. R t t \<and> R t x}) \<le> real (card {t. R t t \<and> R t y})" by auto
    qed
  qed
qed

lemma no_outside_x: "R x x \<longrightarrow> x \<in> alts"
  by (meson alts_rel finite_total_preorder_on_def preorder_on.not_outside(2) total_preorder_on_def)


(*** Theorem 1 (i) <-> (ii) ***)
theorem frac_SDA_utility: 
  "p \<succeq>[SDA(R)] q \<longleftrightarrow> 
  (\<forall>u. vnm_utility alts R u \<longrightarrow> sum_utility u alts p \<ge> sum_utility u alts q)"
proof (unfold SDA_def, rule iffI)
  from alts_rel have "finite alts" 
    unfolding finite_total_preorder_on_def finite_total_preorder_on_axioms_def
    by auto
  from this nonempty_a have fna: "finite_nonempty alts" by (simp add: finite_n_imp_old)
  from alts_rel have "total_preorder_on alts R" 
    unfolding finite_total_preorder_on_def by simp
  hence tot: "\<forall>x \<in> alts. \<forall>y \<in> alts. R x y \<or> R y x"
    unfolding total_preorder_on_axioms_def total_preorder_on_def by auto
  from `total_preorder_on alts R` have trans: "\<forall>x \<in> alts. \<forall>y \<in> alts. \<forall>z \<in> alts. (R x y \<and> R y z \<longrightarrow> R x z)"
    unfolding total_preorder_on_def preorder_on_def by blast
  from tot trans have tton: "total_transitive_on R alts" 
    unfolding total_transitive_on_def by blast
  from fna tton exists_ordered_seq[of "alts" "R"] 
  have "\<exists>a :: nat \<Rightarrow> 'alt. ((\<forall>i j. 
      (1 \<le> i \<and> i \<le> card alts \<and> 1 \<le> j \<and> j \<le> card alts \<longrightarrow> (i < j \<longrightarrow> a j \<succeq>[R] a i))) 
      \<and> (\<forall>i. 1 \<le> i \<and> i \<le> card alts \<longrightarrow>a i \<in> alts) 
      \<and> inj_on a {1..card alts})" 
    by simp
  from this obtain a :: "nat \<Rightarrow> 'alt" where "(\<forall>i j. 
      (1 \<le> i \<and> i \<le> card alts \<and> 1 \<le> j \<and> j \<le> card alts \<longrightarrow> (i < j \<longrightarrow> a j \<succeq>[R] a i))) 
      \<and> (\<forall>i. 1 \<le> i \<and> i \<le> card alts \<longrightarrow>a i \<in> alts) 
      \<and> inj_on a {1..card alts}" 
    by auto

   (* Obtain a function that maps a natural number to the set of alts
      or, obtain a sequence of increasingly preferred alts*)
  hence mono: "(\<forall>i j. 
      (1 \<le> i \<and> i \<le> card alts \<and> 1 \<le> j \<and> j \<le> card alts \<longrightarrow> (i < j \<longrightarrow> a j \<succeq>[R] a i)))"
      and map_alts: "\<forall>i. 1 \<le> i \<and> i \<le> card alts \<longrightarrow>a i \<in> alts"
      and inj: "inj_on a {1..card alts}"
    by auto
  (* Prove that the function mapping is total, hence, it is a sequence. *)
  have totmap: "\<forall>m \<in> alts. \<exists>i. 1 \<le> i \<and> i \<le> card alts \<and> a i = m" 
  proof (rule ccontr)
    assume "\<not> (\<forall>m\<in>alts. \<exists>i. 1 \<le> i \<and> i \<le> card alts \<and> a i = m)"
    hence "\<exists>m \<in> alts. \<forall>i.( 1 \<le> i \<and> i \<le> card alts )\<longrightarrow> a i \<noteq> m" by auto
    hence mnotin: "\<exists>m \<in> alts. m \<notin> a ` {1..card alts}" by force
    from map_alts have subsimg: "a ` {1..card alts} \<subseteq> alts" by auto
    from mnotin subsimg have img_sub_alts: "a ` {1..card alts} \<subset> alts" by auto
    from `finite alts` img_sub_alts psubset_card_mono 
    have img_less_alts: "card (a ` {1..card alts}) < card alts"
      by auto
    from inj have "card {1..card alts} \<le> card (a ` {1..card alts})"
      by (simp add: inj_on_iff_eq_card)
    from this img_less_alts have card_le: "card {1..card alts} < card alts" by simp
    have "card {1..card alts} = card alts" by auto
    from this card_le show False by auto
  qed
  from this inj have surj_a: "\<forall>m \<in> alts. \<exists>!i. 1 \<le> i \<and> i \<le> card alts \<and> a i = m"
    unfolding inj_on_def using atLeastAtMost_iff by blast
  have surjective_a: "a ` {1..card alts} = alts" unfolding image_def
  proof (rule equalityI, rule subsetI)
    fix t
    assume "t \<in> {y. \<exists>x\<in>{1..card alts}. y = a x}"
    hence "\<exists>x \<in> {1..card alts}. t = a x" by auto
    from this obtain x where x_cond: "x\<in>{1..card alts} \<and> t = a x" by auto
    hence "1 \<le> x \<and> x \<le> card alts" by auto
    from this map_alts have "a x  \<in> alts" by simp
    from this x_cond show "t \<in> alts" by simp
  next 
    show "alts \<subseteq> {y. \<exists>x\<in>{1..card alts}. y = a x}"
    proof (rule subsetI, rule CollectI)
      fix t
      assume "t \<in> alts"
      from this surj_a have "\<exists>i. 1 \<le> i \<and> i \<le> card alts \<and> a i = t" by auto
      from this obtain i where i_cond: "1 \<le> i \<and> i \<le> card alts \<and> a i = t" by auto
      hence "i \<in> {1..card alts}" by auto
      from this i_cond have "i \<in> {1..card alts} \<and> t = a i" by auto
      thus "\<exists>xa\<in>{1..card alts}. t = a xa" by auto
    qed
  qed
  from this inj have bijective_a: "bij_betw a {1..card alts} alts"
    by (simp add: bij_betw_def)
  assume sd_prop: "\<forall>x. R x x \<longrightarrow> sum q {y. R y y \<and> R x y} \<le> sum p {y. R y y \<and> R x y}"
  show "\<forall>u. vnm_utility alts R u \<longrightarrow> sum_utility u alts q \<le> sum_utility u alts p"
  proof (rule allI, rule impI)
    fix u
    assume utl: "vnm_utility alts R u"
    hence ord_in_alts: "\<forall>x \<in> alts.\<forall> y \<in> alts. u x \<le> u y \<longleftrightarrow> x \<preceq>[R] y"
      by (simp add: vnm_utility.utility_le_iff)
    let "?SUM" = "sum_utility u alts (p - q)" 
    have "sum_utility u alts (p - q) \<ge> 0" 
    proof -
      let "?f" = "(\<lambda>x. p x - q x)"
      have "p - q = ?f" by auto
      from sum_utility_def this have BSUM_def: "?SUM = (\<Sum>i \<in> alts. u i * ?f i)" by auto
      let "?n" = "card alts"
      from surj_a have surj_map_sum: "(\<Sum>i \<in> alts. u i * ?f i) = (\<Sum>k \<in> {1..card alts}. u (a k) * ?f (a k))"
        using inj sum.reindex_cong surjective_a by fastforce
      define Sf where "Sf i = (\<Sum>k \<in> {1..i}. ?f (a k))" for i 
      from tot have "\<forall>x \<in> alts. \<forall>y \<in> alts. \<not> R x y \<longrightarrow> R y x" by auto
      have reflalts: "\<forall>x \<in> alts. R x x" using tot by blast
      from this sd_prop have def_Sd: "\<forall>x \<in> alts. sum q {y. R y y \<and> R x y} \<le> sum p {y. R y y \<and> R x y}" by auto
      from reflalts no_outside_x have "\<forall>x. R x x \<longleftrightarrow> x \<in> alts" by auto
      hence  "\<forall>x \<in> alts. \<forall>u :: ('alt \<Rightarrow> real). sum u {y. R y y \<and> R x y} = sum u {y \<in> alts. R x y}"
        by auto
      from def_Sd this have sumlarge: "\<forall>x \<in> alts. sum q {y \<in> alts. R x y} \<le> sum p {y \<in> alts. R x y}" by auto
      have abel_sum: "(\<Sum>k \<in> {1..card alts}. u (a k) * ?f (a k)) =
        u (a 1) * (\<Sum>j \<in> {1..card alts}. ?f (a j)) 
      + (\<Sum>j \<in> {2..card alts}. ((u (a j) - u (a (j-1))) * (\<Sum>l \<in> {j..card alts}. ?f (a l))))"
      proof -
        from `finite alts` `alts \<noteq> {}` have "card alts \<ge> (1::nat)"
          using card_0_eq linorder_not_less by auto
        hence exist_func: "\<forall>f g :: (nat \<Rightarrow> real). (\<Sum>i = 1..card alts. f i * g i) =
          f 1 * sum g {1..card alts} + (\<Sum>j = 2..card alts. (f j - f (j - 1)) * sum g {j..card alts})"
          using abel_summation[of "card alts"]
          by auto
        define f where "f i = u (a i)" for i::nat
        define g where "g i = ?f (a i)" for i::nat
        from f_def g_def exist_func show ?thesis by auto  
      qed
      from surj_a have bij: "(\<Sum>l \<in> alts. ?f l) = (\<Sum>j \<in> {1..card alts}. ?f (a j)) " 
        using inj sum.reindex_cong surjective_a by fastforce
      from sum_prob have "(\<Sum>l \<in> alts. ?f l) = 0"
        by (simp add: sum_subtractf)
      from this bij have "(\<Sum>j \<in> {1..card alts}. ?f (a j)) = 0" by auto
      hence sum_first_all_sing: "u (a 1) * (\<Sum>j \<in> {1..card alts}. ?f (a j)) = 0" by auto
      have "\<forall>j \<in> {2..card alts}. (u (a j) - u (a (j-1))) * (\<Sum>l \<in> {j..card alts}. ?f (a l)) \<ge> 0"
      proof (rule ballI)
        fix j
        assume jset: "j \<in> {2..card alts}"
        show "0 \<le> (u (a j) - u (a (j - 1))) * (\<Sum>l = j..card alts. p (a l) - q (a l))"
        proof (cases "\<exists>k. 1 \<le> k \<and> k < j \<and> a k \<succeq>[R] a j")
          case True
          from this obtain k where "1 \<le> k \<and> k < j \<and> a k \<succeq>[R] a j" by auto
          hence "1 \<le> k" and "k < j" and "a k \<succeq>[R] a j" by auto
          from this ord_in_alts have kmore: "u (a k) \<ge> u (a j)"
            by (meson utl vnm_utility.utility_le)
          from `k < j` have "k \<le> j-1" by auto
          thus ?thesis
          proof (cases "k = j - 1")
            case True
            hence "a k = a (j-1)" by simp
            have kl: "a k \<in> alts" 
              by (meson \<open>R (a j) (a k)\<close> \<open>total_preorder_on alts R\<close> 
                  total_preorder_on_def preorder_on.not_outside(2))
            from jset have jl: "a j \<in> alts" by (simp add: map_alts)
            from kl jl `k < j` mono have "a k \<preceq>[R] a j" using \<open>1 \<le> k\<close> jset by force
            hence "u (a k) \<le> u (a j)"  using jl kl ord_in_alts by blast
            from this kmore have "u (a k) = u (a j)" by auto
            from this `a k = a (j - 1)` have "u (a j) = u (a (j-1))" by auto
            hence "u (a j) - u (a (j - 1)) = 0" by auto
            thus ?thesis by simp
          next
            case False
            from this `k < j` have "k < j-1" by auto
            from this mono have "a k \<preceq>[R] a (j-1)"
              by (meson \<open>1 \<le> k\<close> \<open>k \<le> j - 1\<close> atLeastAtMost_iff diff_le_self dual_order.trans jset)
            hence klj1: "u (a k) \<le> u (a (j-1))"
              by (meson utl vnm_utility.utility_le)
            have "j-1 < j"
              using True by force
            hence "a (j-1) \<preceq>[R] a j"
              using \<open>1 \<le> k \<and> k < j \<and> R (a j) (a k)\<close> \<open>k \<le> j - 1\<close> jset mono by force
            hence j1l:"u (a (j-1)) \<le> u (a j)"
              by (meson utl vnm_utility.utility_le)
            from klj1 j1l have "u (a k) \<le> u (a j)" by auto
            from this kmore have "u (a k) = u (a j)" by auto
            from this klj1 j1l have "u (a (j-1)) = u (a j)" by simp
            hence "u (a j) - u (a (j - 1)) = 0" by auto
            thus ?thesis by simp
          qed
        next
          case False
          from False have lsm: "\<forall>k. 1 \<le> k \<and> k < j \<longrightarrow> \<not> a k \<succeq>[R] a j" by auto
          have mla: "\<forall>k. j < k \<and> k \<le> card alts \<longrightarrow> a j \<preceq>[R] a k"
            using jset mono by auto

          from inj have newinj: "inj_on a {2..card alts}" 
            by (metis atLeastatMost_subset_iff inj_on_subset le_refl one_le_numeral)
          have newsurj: "a ` {j..card alts} = {y. R (a j) y \<and> R y y}" 
          proof (unfold image_def, rule equalityI, rule subsetI)
            fix x
            assume "x \<in> {y. \<exists>x\<in>{j..card alts}. y = a x}"
            hence "\<exists>t\<in>{j..card alts}. x = a t" by auto
            from this obtain t where "t \<in> {j..card alts} \<and> x = a t" by auto
            hence "j \<le> t \<and> t \<le> card alts \<and> x = a t" by auto
            hence "a t \<in> alts" using map_alts
              using jset by fastforce
            from this reflalts have "R (a t) (a t)" by auto
            moreover from this reflalts mla have "R (a j) (a t)" 
              using \<open>j \<le> t \<and> t \<le> card alts \<and> x = a t\<close> le_eq_less_or_eq by auto
            ultimately have "R (a t) (a t) \<and> R (a j) (a t)" by auto
            hence "a t \<in> {y. R (a j) y \<and> R y y}" by auto
            thus "x \<in> {y. R (a j) y \<and> R y y}" 
              using \<open>t \<in> {j..card alts} \<and> x = a t\<close> by force
          next
            show "{y. R (a j) y \<and> R y y} \<subseteq> {y. \<exists>x\<in>{j..card alts}. y = a x}" 
            proof (rule subsetI, rule CollectI)
              fix x
              assume "x \<in> {y. R (a j) y \<and> R y y}"
              hence "R (a j) x \<and> R x x" by auto
              hence "R (a j) x" and "R x x" by auto
              from `R x x` have "x \<in> alts"
                using \<open>\<forall>x. R x x = (x \<in> alts)\<close> by blast
              from totmap this have "\<exists>k. 1\<le>k \<and> k \<le> card alts \<and> a k = x" by auto
              from this obtain k where "1 \<le> k \<and> k \<le> card alts \<and> a k = x" by auto
              hence "1 \<le> k" and "k \<le> card alts" and "a k = x" by auto
              have "k \<ge> j"
              proof (rule ccontr)
                assume "\<not> k \<ge> j"
                hence "k < j" by auto
                from this `1 \<le> k` lsm have "\<not> R (a j) (a k)" by auto
                from this `a k = x` have "\<not> R (a j) x" by simp
                from this `R (a j) x` show False by auto
              qed
              from this `k \<le> card alts` have "k \<in> {j..card alts}" by auto
              from this `a k = x` show "\<exists>xa\<in>{j..card alts}. x = a xa" by auto
            qed
          qed

          from newinj newsurj sum.reindex_cong 
          have sum_map: "sum ?f {y. R (a j) y \<and> R y y} = (\<Sum>l \<in> {j..card alts}. ?f (a l))" 
            by (smt (verit, ccfv_SIG) atLeastAtMost_iff basic_trans_rules(23) inj_on_def jset)
          from jset have "a j \<in> alts"
            by (simp add: map_alts)
          from this reflalts have "R (a j) (a j)" by auto
          from this sd_prop have "sum q {y. R y y \<and> R (a j) y} \<le> sum p {y. R y y \<and> R (a j) y}" by auto
          hence "sum ?f {y. R y y \<and> R (a j) y} \<ge> 0"
            by (simp add: sum_subtractf)
          from this sum_map have lmpa: "(\<Sum>l \<in> {j..card alts}. ?f (a l)) \<ge> 0"
            by (metis (mono_tags, lifting) Collect_cong)
          from mono jset have "R (a (j-1)) (a j)"
            using le_simps(3) by force
          from this jset ord_in_alts have "u (a (j-1)) \<le> u (a j)"
            by (meson utl vnm_utility.utility_le)
          hence "u (a j) - u (a (j-1)) \<ge> 0" by auto
          from this lmpa show ?thesis by auto
        qed
      qed
      from this 
      have "(\<Sum>j = 2..card alts. (u (a j) - u (a (j - 1))) * (\<Sum>l = j..card alts. p (a l) - q (a l))) \<ge> 0"
        by (meson sum_nonneg)
      from this sum_first_all_sing abel_sum have "(\<Sum>k \<in> {1..card alts}. u (a k) * ?f (a k)) \<ge> 0"
        by linarith
      from this surj_map_sum have "(\<Sum>i\<in>alts. u i * (p i - q i)) \<ge> 0" by auto
      from this BSUM_def show ?thesis by auto
    qed
    from this
    have "(\<Sum>i \<in> alts. u i * p i - u i * q i) \<ge> 0"
      by (smt (verit, best) Rings.ring_distribs(4) minus_apply sum.cong sum_utility_def)
    thus "sum_utility u alts q \<le> sum_utility u alts p" unfolding sum_utility_def
      by (simp add: sum_subtractf)
  qed
next
  show "\<forall>u. vnm_utility alts R u \<longrightarrow> sum_utility u alts q \<le> sum_utility u alts p \<Longrightarrow>
    \<forall>x. R x x \<longrightarrow> sum q {y. R y y \<and> R x y} \<le> sum p {y. R y y \<and> R x y}"
  proof -
    assume asmp: "\<forall>u. vnm_utility alts R u \<longrightarrow> sum_utility u alts q \<le> sum_utility u alts p"
    show "\<forall>x. R x x \<longrightarrow> sum q {y. R y y \<and> R x y} \<le> sum p {y. R y y \<and> R x y}"
    proof (rule allI, rule impI)
      fix x
      assume "R x x"
      hence "x \<in> alts" using no_outside_x by blast
      define f:: "'alt \<Rightarrow> real" where "f = (\<lambda>x. card {y. R y y \<and> R y x})"
      from f_def card_utility_func have f_ults: "vnm_utility alts R f" by auto
      define g :: "'alt \<Rightarrow> real" where "g = (\<lambda>y. (if y \<succeq>[R] x then 1 else 0))"
      define u :: "real \<Rightarrow> 'alt \<Rightarrow> real" where "u \<epsilon> l = g l + \<epsilon> * f l" for \<epsilon> l 
      have "\<forall>\<epsilon>::real > 0. vnm_utility alts R (u \<epsilon>)"
      proof (rule allI, rule impI)
        fix \<epsilon> :: real
        assume "\<epsilon> > 0"
        show "vnm_utility alts R (u \<epsilon>)"
        proof (unfold vnm_utility_def vnm_utility_axioms_def, rule conjI)
          from alts_rel show "finite_total_preorder_on alts R" by -
          show "\<forall>x y. x \<in> alts \<longrightarrow> y \<in> alts \<longrightarrow> (u \<epsilon> x \<le> u \<epsilon> y) = R x y"
          proof (rule allI, rule allI, rule impI, rule impI)
            fix m n
            assume ma: "m \<in> alts"
            assume na: "n \<in> alts"
            show "(u \<epsilon> m \<le> u \<epsilon> n) = R m n"
            proof (rule iffI)
              assume "u \<epsilon> m \<le> u \<epsilon> n"
              from u_def this have msn: "g m + \<epsilon> * f m \<le> g n + \<epsilon> * f n" by auto
              thus "R m n"
              proof (cases "m \<succeq>[R] x")
                case True
                from this g_def have "g m = 1" by auto
                thus ?thesis
                proof (cases "n \<succeq>[R] x")
                  case True
                  from this g_def have "g n = 1" by auto
                  from `g m = 1` this have "g m = g n" by auto
                  from this `g m + \<epsilon> * f m \<le> g n + \<epsilon> * f n` have "\<epsilon> * f m \<le> \<epsilon> * f n" by auto
                  from this `\<epsilon> > 0` have "f m \<le> f n" by auto
                  from this f_ults ma na show "R m n" 
                    by (simp add: vnm_utility.utility_le_iff)
                next
                  case False
                  from this g_def have "g n = 0" by auto
                  from False have "R n x"
                    by (metis \<open>x \<in> alts\<close> alts_rel finite_total_preorder_on.axioms(1) na total_preorder_on.total)
                  from this True have "R n m"
                    using card_impl_rel card_less_set na by blast
                  from this f_ults have "f m \<ge> f n" 
                    by (simp add: vnm_utility.utility_le)
                  from this `\<epsilon> > 0` `g m = 1` `g n = 0` have "g m + \<epsilon> * f m > g n + \<epsilon> * f n"
                    by (simp add: add_strict_increasing)
                  from this msn have False by auto
                  thus ?thesis by auto
                qed
              next
                case False
                hence "R m x"
                  by (metis \<open>x \<in> alts\<close> alts_rel finite_total_preorder_on.axioms(1) ma total_preorder_on.total)
                from False g_def have "g m = 0" by auto
                thus ?thesis 
                proof (cases "n \<succeq>[R] x")
                  case True
                  from this `R m x` show "R m n" 
                    using card_impl_rel card_less_set ma by blast
                next
                  case False
                  hence "R n x"
                    by (metis \<open>x \<in> alts\<close> alts_rel finite_total_preorder_on.axioms(1) na total_preorder_on.total)
                  from False g_def have "g n = 0" by auto
                  from this `g m = 0` have "g m = g n" by auto
                  from this msn have "\<epsilon> * f m \<le> \<epsilon> * f n" by auto
                  from this `\<epsilon> > 0` have "f m \<le> f n" by auto
                  thus ?thesis 
                    by (meson f_ults ma na vnm_utility.utility_le_iff)
                qed
              qed
            next
              show "R m n \<Longrightarrow> u \<epsilon> m \<le> u \<epsilon> n"
              proof (unfold u_def)
                assume "R m n"
                show "g m + \<epsilon> * f m \<le> g n + \<epsilon> * f n"
                proof (cases "m \<succeq>[R] x")
                  case True
                  from this g_def have "g m = 1" by auto
                  thus ?thesis 
                  proof (cases "n \<succeq>[R] x")
                    case True
                    from this g_def have "g n = 1" by auto
                    from this `g m = 1` have "g m = g n" by auto
                    from `R m n` f_ults have "f m \<le> f n" 
                      by (simp add: vnm_utility.utility_le)
                    from this `\<epsilon> > 0` `g m = g n` show ?thesis by simp
                  next
                    case False
                    from `R m n` True have "R x n" 
                      using \<open>x \<in> alts\<close> card_impl_rel card_less_set by blast
                    from this False have False by auto
                    thus ?thesis by auto
                  qed
                next
                  case False
                  from this g_def have "g m = 0" by auto
                  from False have "R m x"
                    by (metis \<open>x \<in> alts\<close> ma total_preorder_on.total 
                              alts_rel finite_total_preorder_on_def)
                  thus ?thesis 
                  proof (cases "n \<succeq>[R] x")
                    case True
                    from this g_def have "g n = 1" by auto
                    from this `g m = 0` have "g m < g n" by auto
                    from `R m n` f_ults have "f m \<le> f n"
                      by (simp add: vnm_utility.utility_le)
                    from `g m < g n` have "g m \<le> g n" by simp
                    from `\<epsilon> > 0` have "0 \<le> \<epsilon>" by simp
                    from `g m \<le> g n` `\<epsilon> \<ge> 0` `f m \<le> f n` show ?thesis
                      by (simp add: add_mono mult_left_mono)
                  next
                    case False
                    from this g_def have "g n = 0" by auto
                    from this `g m = 0` have "g m = g n" by auto
                    from False have "R n x" 
                      by (metis \<open>x \<in> alts\<close> alts_rel finite_total_preorder_on.axioms(1) na total_preorder_on.total)
                    from `R m n` f_ults have "f m \<le> f n"
                      by (simp add: vnm_utility.utility_le)
                    from this `g m = g n` `\<epsilon> > 0` show ?thesis by auto
                  qed
                qed
                qed
              qed
            qed
          qed
        qed
        from this asmp have "\<forall>\<epsilon> > 0. sum_utility (u \<epsilon>) alts q \<le> sum_utility (u \<epsilon>) alts p" 
          by auto
        hence "\<forall>\<epsilon> > 0. (\<Sum>i \<in> alts. u \<epsilon> i * q i) \<le> (\<Sum>i \<in> alts. u \<epsilon> i * p i)" 
          unfolding sum_utility_def by auto
        hence "\<forall>\<epsilon> > 0. (\<Sum>i \<in> alts. u \<epsilon> i * p i - u \<epsilon> i * q i) \<ge> 0"
          by (simp add: sum_subtractf)
        hence mix_falts: "\<forall>\<epsilon> > 0. (\<Sum>i \<in> alts. u \<epsilon> i * (p i - q i)) \<ge> 0" 
          by (metis (no_types, lifting) Rings.ring_distribs(4) sum.cong)
        have "\<forall>i \<in> alts. R x i \<or> \<not> R x i" by auto
        have "\<forall>x. x \<in> alts \<longleftrightarrow> R x x"
          using card_impl_rel no_outside_x by blast
        hence "{x. R x x} = alts" by blast
        hence "\<forall>\<epsilon>. (\<Sum>i \<in> alts. u \<epsilon> i * (p i - q i)) = (\<Sum>i \<in> {t. R t t}. u \<epsilon> i * (p i - q i))"
          by simp
        from u_def 
        have "\<forall>\<epsilon>. (\<Sum>i \<in> alts. u \<epsilon> i * (p i - q i)) = (\<Sum>i \<in> alts. (g i + \<epsilon> * f i) * (p i - q i))" 
          by auto
        moreover 
        have "\<forall>\<epsilon>. (\<Sum>i \<in> alts. (g i + \<epsilon> * f i) * (p i - q i)) = 
                 (\<Sum>i \<in> alts. g i * (p i - q i) + \<epsilon> * f i* (p i - q i))" 
          by (meson ring_class.ring_distribs(2))
        moreover 
        have "\<forall>\<epsilon>. (\<Sum>i \<in> alts. g i * (p i - q i) + \<epsilon> * f i* (p i - q i)) = 
          (\<Sum>i \<in> alts. g i  * (p i - q i))
        + (\<Sum>i \<in> alts. \<epsilon> * f i * (p i - q i))" 
          by (simp add: sum.distrib)
        moreover 
        have "\<forall>\<epsilon>. (\<Sum>i \<in> alts. \<epsilon> * f i * (p i - q i)) = \<epsilon> * (\<Sum>i \<in> alts. f i * (p i - q i))"
          by (simp add: ab_semigroup_mult_class.mult_ac(1) sum_distrib_left)
        ultimately have f_and_g_sum: "\<forall>\<epsilon>. (\<Sum>i\<in>alts. u \<epsilon> i * (p i - q i)) = 
          (\<Sum>i \<in> alts. g i  * (p i - q i))
        + \<epsilon> * (\<Sum>i \<in> alts. f i * (p i - q i))" by arith

        have "{t. R t t} = {t. R t t \<and> R x t} \<union> {t. R t t \<and> \<not> R x t}" by fastforce
        moreover 
        have "{t. R t t \<and> R x t} \<inter> {t. R t t \<and> \<not> R x t} = {}" by auto
        ultimately 
        have div_sum_out: "(\<Sum>i \<in> {t. R t t}. g i * (p i - q i)) = 
          (\<Sum>i \<in> {t. R t t \<and> R x t}. g i * (p i - q i))
        + (\<Sum>i \<in> {t. R t t \<and> \<not> R x t}. g i * (p i - q i))" 
          by (metis (mono_tags, lifting) \<open>{x. R x x} = alts\<close> 
                    ra_q random_allocation_def sum_Un_eq)
        have "\<forall>i \<in> {t. R t t \<and> R x t}. g i = 1" 
          unfolding g_def by force
        hence summore: "(\<Sum>i \<in> {t. R t t \<and> R x t}. g i * (p i - q i)) = 
          (\<Sum>i \<in> {t. R t t \<and> R x t}. (p i - q i))" 
          by auto
        have "\<forall>i \<in> {t. R t t \<and> \<not> R x t}. g i = 0" 
          unfolding g_def by force
        hence sumless: "(\<Sum>i \<in> {t. R t t \<and> \<not> R x t}. g i * (p i - q i)) = 0" 
          by simp
        from summore sumless div_sum_out 
        have "(\<Sum>i \<in> {t. R t t}. g i * (p i - q i)) = 
              (\<Sum>i \<in> {t. R t t \<and> R x t}. (p i - q i))" 
          by auto
        from this f_and_g_sum 
        have sep_eps: "\<forall>\<epsilon>. (\<Sum>i\<in>alts. u \<epsilon> i * (p i - q i)) = 
                           (\<Sum>i\<in>{t. R t t \<and> R x t}. p i - q i) + 
                             \<epsilon> * (\<Sum>i\<in>alts. f i * (p i - q i))" 
          using `{x. R x x} = alts` by simp
        let "?A" = "(\<Sum>i\<in>{t. R t t \<and> R x t}. p i - q i)"
        let "?B" = "(\<Sum>i\<in>alts. f i * (p i - q i))"
        from sep_eps have "\<forall>\<epsilon>. (\<Sum>i\<in>alts. u \<epsilon> i * (p i - q i)) = ?A + \<epsilon> * ?B" by -
        from mix_falts this have eps_all_nonneg: "\<forall>\<epsilon> > 0. ?A + \<epsilon> * ?B \<ge> 0" by auto
        with first_order_nonneg have "?A \<ge> 0" by blast
        thus "sum p {t. R t t \<and> R x t} \<ge> sum q {t. R t t \<and> R x t}" 
          by (simp add: sum_subtractf)
      qed
    qed
  qed

theorem not_strict_SDA_utility:
 "\<not> (q \<succ>[SDA(R)] p) \<longleftrightarrow> (\<exists>u. vnm_utility alts R u \<and> sum_utility u alts p \<ge> sum_utility u alts q)"
proof (rule iffI)
  have rpq: "random_pair_allocation alts p q R" 
    using random_pair_allocation_axioms by blast
  have rqp: "random_pair_allocation alts q p R" 
    by (simp add: alts_rel nonempty_a ra_p ra_q random_pair_allocation_def sum_prob)
  assume qnotstrict: "\<not> p \<prec>[SDA R] q"
  show "\<exists>u. vnm_utility alts R u \<and> sum_utility u alts q \<le> sum_utility u alts p"
  proof -
    from qnotstrict strongly_preferred_def[of "p" "SDA (R)" "q"] have  "\<not> p \<preceq>[SDA(R)] q \<or> q \<preceq>[SDA(R)] p" by auto
    from this rqp rpq random_pair_allocation.frac_SDA_utility[of "alts" "p" "q" "R"]
      random_pair_allocation.frac_SDA_utility[of "alts" "q" "p" "R"]
    have "\<not> (\<forall>u. vnm_utility alts R u \<longrightarrow> sum_utility u alts p \<le> sum_utility u alts q) \<or> 
        (\<forall>u. vnm_utility alts R u \<longrightarrow> sum_utility u alts q \<le> sum_utility u alts p)" by auto
    hence ors: "(\<exists>u. vnm_utility alts R u \<and> sum_utility u alts p > sum_utility u alts q) \<or>
        (\<forall>u. vnm_utility alts R u \<longrightarrow> sum_utility u alts q \<le> sum_utility u alts p)" by auto
    from card_utility_func have "\<exists>u. vnm_utility alts R u" by auto
    from this ors show "\<exists>u. vnm_utility alts R u \<and> sum_utility u alts p \<ge> sum_utility u alts q" by auto
  qed
next
  have rpq: "random_pair_allocation alts p q R" 
    using random_pair_allocation_axioms by blast
  have rqp: "random_pair_allocation alts q p R" 
    by (simp add: alts_rel nonempty_a ra_p ra_q random_pair_allocation_def sum_prob)
  assume oneleq: "\<exists>u. vnm_utility alts R u \<and> sum_utility u alts q \<le> sum_utility u alts p"
  show "\<not> p \<prec>[SDA R] q"
  proof (rule ccontr)
    assume "\<not> \<not> p \<prec>[SDA R] q"
    hence "p \<prec>[SDA R] q" by auto
    from this strongly_preferred_def have "p \<preceq>[SDA R] q \<and> \<not> q \<preceq>[SDA R] p"
      by metis
    from this rqp rpq random_pair_allocation.frac_SDA_utility[of "alts" "p" "q" "R"]
      random_pair_allocation.frac_SDA_utility[of "alts" "q" "p" "R"]
    have "(\<forall>u. vnm_utility alts R u \<longrightarrow> sum_utility u alts p \<le> sum_utility u alts q) \<and>
    \<not> (\<forall>u. vnm_utility alts R u \<longrightarrow> sum_utility u alts q \<le> sum_utility u alts p)" by auto
    hence "(\<forall>u. vnm_utility alts R u \<longrightarrow> sum_utility u alts p \<le> sum_utility u alts q) \<and>
    (\<exists>u. vnm_utility alts R u \<and> sum_utility u alts q > sum_utility u alts p)" by auto
    hence alleq: "(\<forall>u. vnm_utility alts R u \<longrightarrow> sum_utility u alts p \<le> sum_utility u alts q)" and
      onestr: "(\<exists>u. vnm_utility alts R u \<and> sum_utility u alts q > sum_utility u alts p)" by auto
    from oneleq alleq obtain u where "vnm_utility alts R u \<and> sum_utility u alts q = sum_utility u alts p"
      by auto
    hence "vnm_utility alts R u" and ueq: "sum_utility u alts q = sum_utility u alts p" by auto
    from onestr obtain u1 where "vnm_utility alts R u1 \<and> sum_utility u1 alts q > sum_utility u1 alts p" by auto
    hence "vnm_utility alts R u1" and u1la: "sum_utility u1 alts q > sum_utility u1 alts p" by auto
    have "\<And>x y. R x y \<Longrightarrow> R y x \<Longrightarrow> u1 x = u1 y"
      by (smt (verit, best) \<open>vnm_utility alts R u1\<close> vnm_utility.utility_le)
    from vnm_utility.diff_epsilon this `vnm_utility alts R u` 
    have "\<exists>\<epsilon>>0. vnm_utility alts R (\<lambda>x. u x - \<epsilon> * u1 x)"
      by blast
    from this obtain \<epsilon> where epsl: "\<epsilon> > 0" and newult: "vnm_utility alts R (\<lambda>x. u x - \<epsilon> * u1 x)" by auto
    define u2 where "u2 = (\<lambda>x. u x - \<epsilon> * u1 x)"
    from this newult have u2ult: "vnm_utility alts R u2"  by auto
    from u1la epsl have "\<epsilon> * sum_utility u1 alts p < \<epsilon> * sum_utility u1 alts q" by auto
    from ueq this have sumla: "sum_utility u alts p - \<epsilon> * sum_utility u1 alts p > 
      sum_utility u alts q - \<epsilon> * sum_utility u1 alts q" by auto
    { fix p :: "'alt \<Rightarrow> real"
    have "sum_utility u alts p - \<epsilon> * sum_utility u1 alts p = 
        (\<Sum>i\<in>alts. u i * p i) - \<epsilon> * (\<Sum>i \<in> alts. u1 i * p i)"
      unfolding sum_utility_def
      by auto
    moreover have " \<epsilon> * (\<Sum>i \<in> alts. u1 i * p i) = 
          (\<Sum>i \<in> alts. \<epsilon> * u1 i * p i)" 
      by (simp add: sum_distrib_left vector_space_over_itself.scale_scale)
    moreover have "(\<Sum>i\<in>alts. u i * p i) - (\<Sum>i \<in> alts. \<epsilon> * u1 i * p i)
        = (\<Sum>i \<in> alts. u i * p i - \<epsilon> * u1 i * p i)" 
      by (simp add: sum_subtractf)
    moreover have "(\<Sum>i \<in> alts. u i * p i - \<epsilon> * u1 i * p i) = (\<Sum>i \<in> alts. (u i - \<epsilon> * u1 i) * p i)"
      by (simp add: vector_space_over_itself.scale_left_diff_distrib)
    moreover from u2_def have "(\<Sum>i \<in> alts. (u i - \<epsilon> * u1 i) * p i) = (\<Sum>i \<in> alts. u2 i * p i)" by auto
    ultimately have "sum_utility u alts p - \<epsilon> * sum_utility u1 alts p = (\<Sum>i \<in> alts. u2 i * p i)" by auto
  }
  hence "sum_utility u alts p - \<epsilon> * sum_utility u1 alts p = (\<Sum>i\<in>alts. u2 i * p i)" 
    and "sum_utility u alts q - \<epsilon> * sum_utility u1 alts q = (\<Sum>i\<in>alts. u2 i * q i)" by auto
  from this sumla have "(\<Sum>i\<in>alts. u2 i * p i) > (\<Sum>i\<in>alts. u2 i * q i)" by auto
  hence morez: "sum_utility u2 alts p > sum_utility u2 alts q" unfolding sum_utility_def by auto
  from u2ult alleq have leqz: "sum_utility u2 alts p \<le> sum_utility u2 alts q" by auto
  from morez leqz show False by auto
  qed
qed
end


locale discrete_pair_allocation = random_pair_allocation +
  assumes disc_p: "discrete_allocation alts p"
  assumes disc_q: "discrete_allocation alts q"

sublocale discrete_pair_allocation \<subseteq> random_pair_allocation
  by (simp add: random_pair_allocation_axioms)

context discrete_pair_allocation
begin
(*** Theorem 1 (i) <-> (ii) ***)
theorem disc_SDA_utility:
  "p \<succeq>[SDA (R)] q \<longleftrightarrow> 
  (\<forall>u. vnm_utility alts R u \<longrightarrow> sum u (allocated_alts p alts) \<ge> sum u (allocated_alts q alts))" 
by (metis discrete_allocation.sum_ut_eq_sum_alt disc_p disc_q frac_SDA_utility)


(*** Theorem 1 (iii) \<rightarrow> (ii) ***)
theorem RS_to_utility: 
  "allocated_alts p alts \<succeq>[RS(R)] allocated_alts q alts \<Longrightarrow> 
      (\<forall>u. vnm_utility alts R u \<longrightarrow> sum u (allocated_alts p alts) \<ge> sum u (allocated_alts q alts))"
unfolding RS_def
proof (rule allI, rule impI)
  assume "\<exists>f. inj_on f (allocated_alts q alts) \<and>
        f ` allocated_alts q alts \<subseteq> allocated_alts p alts \<and> (\<forall>x\<in>allocated_alts q alts. R x (f x))"
  from this obtain f where "inj_on f (allocated_alts q alts) \<and>
        f ` allocated_alts q alts \<subseteq> allocated_alts p alts \<and> (\<forall>x\<in>allocated_alts q alts. R x (f x))" by auto
  hence injf: "inj_on f (allocated_alts q alts)" and
                mapf: "f ` allocated_alts q alts \<subseteq> allocated_alts p alts" and 
                pref_f: "\<forall>x\<in>allocated_alts q alts. R x (f x)"
    by auto
  from disc_p discrete_allocation.sum_to_card_allocated 
  have pcard: "sum p alts = card (allocated_alts p alts)"
    by auto
  from disc_q discrete_allocation.sum_to_card_allocated 
  have qcard: "sum q alts = card (allocated_alts q alts)"
    by auto
  from sum_prob pcard qcard 
  have "card (allocated_alts p alts) = card (allocated_alts q alts)" 
    by auto
  from mapf this injf 
  have "f ` allocated_alts q alts = allocated_alts p alts"
    by (metis allocated_subset alts_rel card_image card_subset_eq 
              finite_total_preorder_on_iff infinite_super)
  from this injf pref_f sum.reindex_cong
  have umap: "\<forall>u ::('a \<Rightarrow> real). (\<Sum>x \<in> allocated_alts q alts. u (f x)) = (\<Sum>y \<in> allocated_alts p alts. u y)"
    by metis
  fix u
  assume utlu: "vnm_utility alts R u"
  from umap have pmap: "(\<Sum>y \<in> allocated_alts p alts. u y) = (\<Sum>x \<in> allocated_alts q alts. u (f x))" by auto
  have "\<forall>x \<in> allocated_alts q alts. u (f x) \<ge> u x" 
  proof (rule ballI)
    fix x
    assume "x \<in> allocated_alts q alts"
    with utlu pref_f show "u (f x) \<ge> u x" 
      by (simp add: vnm_utility.utility_le)
  qed
  hence "(\<Sum>x \<in> allocated_alts q alts. u (f x)) \<ge> (\<Sum>x \<in> allocated_alts q alts. u x)"
    by (simp add: sum_mono)
  with pmap 
  show "sum u (allocated_alts q alts) \<le> sum u (allocated_alts p alts)" 
    by auto
qed

(* Lemmas for (i) \<rightarrow> (iii) *)
lemma sum_prop_to_count_large:
  fixes x
  assumes "x \<in> alts"
  shows "sum p {y. R y y \<and> y \<succeq>[R] x} = card {y \<in> allocated_alts p alts. y \<succeq>[R] x}"
using assms
proof -
  have sep_alloc: "{y \<in> allocated_alts p alts. R x y} = allocated_alts p alts \<inter> {y. R x y}" 
      by auto
    have to_alts: "{y. R y y \<and> R x y} = {y \<in> alts. R x y}" 
      using card_impl_rel no_outside_x set_eq_subset 
      by blast
    from to_alts have sum_to_alts: "sum p {y. R y y \<and> R x y} = sum p {y \<in> alts. R x y}" 
      by simp
    have zeros_or_ones: "\<forall>y \<in> alts. p y = 0 \<or> p y = 1"
      by (metis discrete_allocation.disc[of "alts" "p"] discrete_pair_allocation_def
          discrete_pair_allocation_axioms discrete_pair_allocation_axioms_def)
    have alts_inter: "{y \<in> alts. R x y} = alts \<inter> {y. R x y}" by auto
    hence sum_alts_inter: "sum p {y \<in> alts. R x y} = sum p (alts \<inter> {y. R x y})" by auto
    have sum_to_seq: "sum p (alts \<inter> {y. R x y}) = (\<Sum>k \<in> (alts \<inter> {y. R x y}). p k)" by auto
    have "alts \<inter> {y. R x y} \<subseteq> alts" by auto

    from allocated_ones this have one_then_allocated: 
      "\<forall>k \<in> alts \<inter> {y. R x y}. (p k = 1 \<longrightarrow> k \<in> allocated_alts p alts)"
      by (metis IntD1 rel_simps(92))
    from zeros_or_ones have disc_alts: "\<forall>k \<in> alts \<inter> {y. R x y}. p k = 0 \<or> p k = 1" by simp
    with allocated_subset have disc_alloc: "\<forall>k \<in> allocated_alts p alts \<inter> {y. R x y}. p k = 0 \<or> p k = 1"
      by fast
    from disc_alts have sum_to_indicator:"(\<Sum>k \<in> (alts \<inter> {y. R x y}). p k) = (\<Sum>k \<in> (alts \<inter> {y. R x y}). 
        (if (p k \<noteq> 0) then real(1) else real(0)))" 
      by (smt (verit, best) Multiseries_Expansion.intyness_0 Multiseries_Expansion.intyness_1 sum.cong)                              
    from one_then_allocated have "\<forall>k \<in> alts \<inter> {y. R x y}. 
      (p k = 1 \<longrightarrow> k \<in> allocated_alts p alts \<inter> {y. R x y})"
      by simp
    with disc_alloc 
    have sum_alts_to_alloc:"(\<Sum>k \<in> (alts \<inter> {y. R x y}). (if (p k \<noteq> 0) then 1 else 0)) = 
      (\<Sum>k \<in> (allocated_alts p alts \<inter> {y. R x y}). (if (p k \<noteq> 0) then 1 else 0))"
      by (smt (verit) DiffE Int_greatest Int_lower2 
allocated_subset alts_rel basic_trans_rules(23) disc_alts finite_subset 
finite_total_preorder_on.finite_carrier inf_le1 sum.mono_neutral_cong_right)
    from allocated_alts_def have sum_to_card:"(\<Sum>k \<in> (allocated_alts p alts \<inter> {y. R x y}). (if (p k \<noteq> 0) then 1 else 0))
      = card {y \<in> allocated_alts p alts. R x y}"
      by (smt (verit, ccfv_SIG) card_eq_sum mem_Collect_eq sep_alloc sum.cong)
    hence sum_real_card: "(\<Sum>k\<in>allocated_alts p alts \<inter> {y. R x y}. if p k \<noteq> 0 then real(1) else real(0)) 
      = real(card {y \<in> allocated_alts p alts. R x y})" 
      by (smt (verit) of_nat_sum sum.cong)
    from sum_to_alts sum_alts_inter sum_to_indicator sum_real_card 
    show "sum p {y. R y y \<and> R x y} = card {y \<in> allocated_alts p alts. R x y}"
      by (metis (no_types, lifting) Multiseries_Expansion.intyness_0 
          Multiseries_Expansion.intyness_1 sum.cong sum_alts_to_alloc)
qed


lemma SDA_to_disc_SDA:
  "p \<succeq>[SDA(R)] q \<longrightarrow>
    (\<forall>x \<in> alts. card {y \<in> allocated_alts p alts. y \<succeq>[R] x} \<ge> 
                 card {y \<in> allocated_alts q alts. y \<succeq>[R] x} )"
proof (rule impI)
  assume sd_pref: "p \<succeq>[SDA(R)] q"
  from this SDA_def[of "R" "q" "p"] 
  have sd_sum: "\<forall>x. R x x \<longrightarrow> sum q {y. R y y \<and> R x y} \<le> sum p {y. R y y \<and> R x y}"
    by simp
  hence "\<forall>x.  x \<in> alts \<longrightarrow> R x x" 
    by (metis total_preorder_on_def discrete_pair_allocation_axioms 
        finite_total_preorder_on_def total_preorder_on_axioms_def
        discrete_pair_allocation_def random_pair_allocation_def)
  with sd_sum have "\<forall>x. x \<in> alts \<longrightarrow> sum q {y. R y y \<and> R x y} \<le> sum p {y. R y y \<and> R x y}"
    by simp
  hence sd_def_alts: "\<forall>x \<in> alts. sum q {y. R y y \<and> R x y} \<le> sum p {y. R y y \<and> R x y}" by auto
  from this
  show "\<forall>x \<in> alts. card {y \<in> allocated_alts p alts. y \<succeq>[R] x} \<ge> card {y \<in> allocated_alts q alts. y \<succeq>[R] x}"
  proof -
    have "\<forall>x \<in> alts. sum q {y. R y y \<and> R x y} \<le> sum p {y. R y y \<and> R x y} \<longrightarrow> 
      card {y \<in> allocated_alts p alts. y \<succeq>[R] x} \<ge> card {y \<in> allocated_alts q alts. y \<succeq>[R] x}" 
    proof (rule ballI)
      fix x
      assume xalt: "x \<in> alts"
      from this sum_prop_to_count_large
      have p_eq: "sum p {y. R y y \<and> R x y} = real (card {y \<in> allocated_alts p alts. R x y})"
        by auto
      have "discrete_pair_allocation alts q q R"
        unfolding discrete_pair_allocation_def discrete_pair_allocation_axioms_def 
                  random_pair_allocation_def
        by (auto simp add: nonempty_a discrete_pair_allocation_def discrete_pair_allocation_axioms_def
                      discrete_pair_allocation_axioms disc_q ra_q alts_rel)
      from this discrete_pair_allocation.sum_prop_to_count_large
      have q_eq: "sum q {y. R y y \<and> R x y} = real (card {y \<in> allocated_alts q alts. R x y})"
        using xalt 
        by fast 
      from p_eq q_eq show "sum q {y. R y y \<and> R x y} \<le> sum p {y. R y y \<and> R x y} \<longrightarrow>
         card {y \<in> allocated_alts q alts. R x y} \<le> card {y \<in> allocated_alts p alts. R x y}"
        by linarith
     qed
     with sd_def_alts show ?thesis 
       by simp
  qed
qed

definition 
  at_least_as_preferred :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set " 
where
  "at_least_as_preferred x u = {y. R x y} \<inter> u"

lemma preferred_empty: "at_least_as_preferred x {} = {}"
  unfolding at_least_as_preferred_def
  by simp

(*** Aziz et al's Theorem 1 (i) \<rightarrow> (iii) ***)
theorem SDA_to_RS:
  "p \<succeq>[SDA(R)] q  \<longrightarrow>
    allocated_alts p alts \<succeq>[RS(R)] allocated_alts q alts"
proof (rule impI)
  assume sda_cond: "p \<succeq>[SDA(R)] q"
  with SDA_to_disc_SDA
  have card_le_alloc:
    "(\<forall>x\<in>alts. card {y \<in> allocated_alts q alts. R x y} \<le> card {y \<in> allocated_alts p alts. R x y})"
    by simp
  define F :: "'a \<Rightarrow> 'a set" 
    where 
    "F = (\<lambda>x. at_least_as_preferred x (allocated_alts p alts))"
  from discrete_pair_allocation_def discrete_pair_allocation_axioms alts_rel nonempty_a have 
        "finite_total_preorder_on alts R" 
    and "alts \<noteq> {}"
    by auto
  with finite_total_preorder_on_def finite_total_preorder_on_axioms_def
    finite_total_preorder_on_axioms_def have "finite alts" by auto
  from allocated_subset have "allocated_alts q alts \<subseteq> alts" by fast
  from `finite alts` `alts \<noteq> {}` this have asm1: "finite (allocated_alts q alts)"
    using finite_subset by blast
  have asm2: "\<forall>i \<in> allocated_alts q alts. finite (F i)" 
  proof (rule ballI)
    fix i
    assume "i \<in> allocated_alts q alts"
    from F_def at_least_as_preferred_def have Fi_sub: "F i \<subseteq> allocated_alts p alts" by auto
    from allocated_subset have "allocated_alts p alts \<subseteq> alts" by force
    with Fi_sub have "F i \<subseteq> alts" by auto
    with `finite alts` `alts \<noteq> {}` show "finite (F i)"
      using finite_subset by blast
  qed
  have asm3: "\<forall>J \<subseteq> allocated_alts q alts. card J \<le> card(\<Union>(F ` J))"
  proof (rule allI, rule impI)
    fix J
    assume subJ: "J \<subseteq> allocated_alts q alts"
    from allocated_subset have "allocated_alts q alts \<subseteq> alts" by fast
    with subJ have "J \<subseteq> alts" by auto
    from discrete_pair_allocation_def discrete_pair_allocation_axioms alts_rel have 
      "finite_total_preorder_on alts R" by auto
    with finite_total_preorder_on_def have "total_preorder_on alts R" by auto
    with total_preorder_on_def have "total_preorder_on_axioms alts R" by auto
    with total_preorder_on_axioms_def have total_z: "\<forall>x y. x \<in> alts \<longrightarrow> y \<in> alts 
      \<longrightarrow> R x y \<or> R y x"
      by metis
    from `total_preorder_on alts R` total_preorder_on_def have "preorder_on alts R" by auto
    with preorder_on_def have transitive_z: "\<forall>x y z. R x y \<longrightarrow> R y z \<longrightarrow> R x z" 
      by metis
    from total_z transitive_z total_transitive_on_def have ttrans: "total_transitive_on R alts" 
      by (metis (full_types))
    with `J \<subseteq> alts` total_transitive_on_subset have ttransJ: "total_transitive_on R J" 
      by auto
    show "card J \<le> card (\<Union> (F ` J))"
    proof (cases "J = {}")
      case True
      hence "F ` J = {}" by auto
      hence "\<Union> (F ` J) = {}" by auto
      with True show "card J \<le> card (\<Union> (F ` J))" by auto
    next
      case False
      from `J \<subseteq> alts` `finite alts` `alts \<noteq> {}` have "finite J" 
        using finite_subset by blast
      with False finite_n_imp_old have "finite_nonempty J" by auto
      with ttransJ exist_minimal_element[of "J" "R"] have
        min_J: "\<exists>x\<in>J. \<forall>y\<in>J. R x y" by simp
      then obtain x where x_in_j: "x \<in> J" and x_is_min: "\<forall>y \<in> J. R x y" by auto
      from x_in_j have ineq1: "card (F x) \<le> card (\<Union> (F ` J))"
        by (meson UN_upper \<open>finite J\<close> asm2 card_mono finite_UN_I subJ subset_iff)
      from min_J F_def at_least_as_preferred_def
      have eq1: "F x = {y \<in> allocated_alts p alts. R x y}" 
        by auto
      from x_in_j `J \<subseteq> alts` have "x \<in> alts" by auto
      from card_le_alloc this have
        ineq2: "card {y \<in> allocated_alts q alts. R x y} \<le> card {y \<in> allocated_alts p alts. R x y}"
        by auto
      from x_is_min x_in_j subJ have "J \<subseteq> {y \<in> allocated_alts q alts. R x y}" by auto
      with `finite (allocated_alts q alts)` 
      have ineq3: "card J \<le> card {y \<in> allocated_alts q alts. R x y}"
        by (simp add: card_mono)
      from ineq1 ineq2 eq1 ineq3 show "card J \<le> card (\<Union> (F ` J))" by auto
    qed 
  qed
  from asm1 asm2 asm3 marriage_HV
  have "\<exists>R. (\<forall>i\<in> allocated_alts q alts. R i \<in> F i) \<and> inj_on R (allocated_alts q alts)"
    by blast
  then obtain f 
    where "(\<forall>i\<in> allocated_alts q alts. f i \<in> F i) \<and> inj_on f (allocated_alts q alts)"
    by auto
  hence f_in_set: "(\<forall>i\<in> allocated_alts q alts. f i \<in> F i)" and 
    RS1: "inj_on f (allocated_alts q alts)"
    by auto
  have RS2:"\<forall>x\<in>allocated_alts q alts. R x (f x)"
  proof (rule ballI)
    fix x
    assume xalloc: "x \<in> allocated_alts q alts"
    with f_in_set have "f x \<in> F x" by auto
    with F_def have "f x \<in> at_least_as_preferred x (allocated_alts p alts)" by auto
    with at_least_as_preferred_def have "f x \<in> {y. R x y}" by auto
    thus "R x (f x)" by auto
  qed
  have RS3:"f ` allocated_alts q alts \<subseteq> allocated_alts p alts" 
  proof (rule subsetI)
    fix x
    assume "x \<in> f ` allocated_alts q alts" 
    hence "\<exists>y \<in> allocated_alts q alts. f y = x" by auto
    from this obtain y where "y \<in> allocated_alts q alts" and "f y = x" by auto
    from F_def at_least_as_preferred_def 
    have F_sub_alloc: "\<forall>x. F x \<subseteq> allocated_alts p alts" by auto
    from f_in_set `f y = x` `y \<in> allocated_alts q alts` have "x \<in> F y" by auto
    from this F_sub_alloc show "x \<in> allocated_alts p alts" by auto
  qed
  from RS1 RS2 RS3 show "allocated_alts p alts \<succeq>[RS(R)] allocated_alts q alts"
    unfolding RS_def
    by auto
qed

(*** Theorem 1 (iii) <-> (ii) ***)
theorem RS_utility:
  "allocated_alts p alts \<succeq>[RS(R)] allocated_alts q alts \<longleftrightarrow> 
      (\<forall>u. vnm_utility alts R u 
          \<longrightarrow> sum u (allocated_alts p alts) \<ge> sum u (allocated_alts q alts))"
proof -
  from RS_to_utility disc_SDA_utility SDA_to_RS show ?thesis by auto
qed

(*** Theorem 1 (i) <-> (iii) ***)
theorem SDA_RS:
  "p  \<succeq>[SDA(R)] q  \<longleftrightarrow>
    allocated_alts p alts \<succeq>[RS(R)] allocated_alts q alts"
proof -
  from disc_SDA_utility RS_utility show ?thesis by auto
qed

lemma SDA_RS_ext:
 "p  \<succeq>[SDA(R)] q \<longleftrightarrow>
  (\<forall>P. (\<forall>s1 s2. RS(R) s1 s2 \<longrightarrow> P s1 s2) \<longrightarrow>
    (allocated_alts p alts \<succeq>[P] allocated_alts q alts))"
proof (rule iffI)
  show "SDA R q p \<Longrightarrow> \<forall>P. (\<forall>s1 s2. RS R s1 s2 \<longrightarrow>  P s1 s2) \<longrightarrow> P (allocated_alts q alts) (allocated_alts p alts)"
  proof -
    assume "p \<succeq>[SDA(R)] q"
    from this SDA_RS have re: "allocated_alts p alts \<succeq>[RS(R)] allocated_alts q alts" by auto
    show "\<forall>P. (\<forall>s1 s2. RS R s1 s2 \<longrightarrow> P s1 s2) \<longrightarrow> P (allocated_alts q alts) (allocated_alts p alts)"
    proof (rule allI, rule impI)
      fix P
      assume "\<forall>s1 s2. RS R s1 s2 \<longrightarrow> P s1 s2"
      from re this show "allocated_alts p alts \<succeq>[P] allocated_alts q alts" by auto
    qed
  qed
next
  show "\<forall>P. (\<forall>s1 s2. RS R s1 s2 \<longrightarrow> P s1 s2) \<longrightarrow> P (allocated_alts q alts) (allocated_alts p alts) \<Longrightarrow> SDA R q p"
  proof -
    assume allp: "\<forall>P. (\<forall>s1 s2. RS R s1 s2 \<longrightarrow> P s1 s2) \<longrightarrow> P (allocated_alts q alts) (allocated_alts p alts)"
    have "\<forall>s1 s2. RS(R) s1 s2 \<longrightarrow> RS(R) s1 s2" by auto
    from this allp have "allocated_alts p alts \<succeq>[RS(R)] allocated_alts q alts" by auto
    from this SDA_RS show "p \<succeq>[SDA(R)] q" by auto
  qed
qed

lemma not_strict_SDA_RS_ext:
  "\<not> (p \<succ>[SDA(R)] q) \<longrightarrow>
    (\<exists>P. (\<forall>s1 s2. RS(R) s1 s2 \<longrightarrow> P s1 s2) \<and>
      (allocated_alts q alts \<succeq>[P] allocated_alts p alts))" 
  by blast

end

context random_assignment
begin

definition 
  pmf_like_set :: "'alt set \<Rightarrow> ('alt \<Rightarrow> real)" 
where
  "pmf_like_set S = (\<lambda>x.(if x \<in> S then 1 / real (card agents) else 0))"

lemma sum_m_over_n: 
  fixes i :: "'agent" 
  assumes "i \<in> agents"
  shows "sum (p i) alts = real (card alts) / real (card agents)"
  using card_0_eq nonzero_divide_eq_eq of_nat_eq_0_iff 
proof - 
  from random_assignment_def pref_profile_wf_def random_assignment_axioms
  have "agents \<noteq> {}" and "finite agents"
    by fast+
  from random_assignment_def have "(\<exists>c. \<forall>i\<in>agents. sum (p i) alts = c)" by auto
  from this obtain c where constc: "\<forall>i \<in> agents. sum (p i) alts = c" by blast
  from constc have "(\<Sum>i \<in> agents. sum (p i) alts) = c * (card agents)" by auto
  moreover have "(\<Sum>i \<in> agents. sum (p i) alts) = (\<Sum>j \<in> alts. (\<Sum>i \<in> agents. p i j))"
    using sum.swap by blast
  moreover from random_assignment_def have "\<forall>j\<in>alts. (\<Sum>i\<in>agents. p i j) = 1" by auto
  moreover hence "(\<Sum>j \<in> alts. (\<Sum>i \<in> agents. p i j)) = real (card alts)" by auto
  ultimately have "c * real (card agents) = real (card alts)" by auto
  from this `agents \<noteq> {}` `finite agents` have "c = real (card alts) / real (card agents)"
    by (metis card_0_eq nonzero_divide_eq_eq of_nat_eq_0_iff)
  from this constc show ?thesis 
    using assms by blast
qed

lemma random_alloc_pmf: "random_allocation alts (pmf_like_set alts)"
proof (unfold random_allocation_def)
  let "?P" = "pmf_like_set alts"
  from random_assignment_def have 1: "finite alts" 
    by (metis pref_profile_wf.finite_alts random_assignment_axioms)
  from pmf_like_set_def have 2: "\<forall>j. j \<notin> alts \<longrightarrow> ?P j = 0" by auto
  from random_assignment_def pref_profile_wf_def
  have "agents \<noteq> {} \<and> finite agents"
    by (metis random_assignment_axioms)
  hence "agents \<noteq> {}" and "finite agents" by auto
  hence "card agents > 0" by auto
  hence "card agents \<ge> 1" by auto
  hence "1 / (real (card agents)) \<le> 1" by auto
  moreover from `card agents \<ge> 1` have "0 \<le> 1 / (real (card agents))" by auto
  ultimately have "0 \<le> 1 / (real (card agents)) \<and> 1 / (real (card agents)) \<le> 1" by auto
  from this pmf_like_set_def have 3: "\<forall>j \<in> alts. 0 \<le> ?P j \<and> ?P j \<le> 1" by auto
  from 1 2 3 show "finite alts \<and>
    (\<forall>j. j \<notin> alts \<longrightarrow> pmf_like_set alts j = 0) \<and> (\<forall>j\<in>alts. 0 \<le> pmf_like_set alts j \<and> pmf_like_set alts j \<le> 1)" 
    by auto
qed

lemma sum_divide_agents: "sum u alts / real (card agents) = sum_utility u alts (pmf_like_set alts)"
proof -
  have "sum u alts / real (card agents) = (\<Sum>i \<in> alts. u i / real (card agents))" 
    using sum_divide_distrib by blast
  moreover have "sum_utility u alts (pmf_like_set alts) = (\<Sum>i \<in> alts. u i *  pmf_like_set alts i)" 
    using sum_utility_def
    by auto
  moreover from pmf_like_set_def have "\<forall>i \<in> alts. pmf_like_set alts i = 1 / real (card agents)" by auto
  moreover have "(\<Sum>i \<in> alts. u i *  1 / real (card agents)) = (\<Sum>i \<in> alts. u i / real (card agents))"
    by auto
  ultimately show "sum u alts / real (card agents) = sum_utility u alts (pmf_like_set alts)" by auto
qed

lemma sum_pmf_like_set: "sum (pmf_like_set alts) alts = real (card alts) / real (card agents)"
proof -
  let "?P" = "pmf_like_set alts"
  from pmf_like_set_def have "(\<forall>i \<in> alts. pmf_like_set alts i = 1 / real (card agents))" by auto
  hence "sum ?P alts = real (card alts) * 1 / real (card agents)" by auto
  thus "sum ?P alts = real (card alts) / real (card agents)" by auto
qed

(* The positions mentioned here are the positions of those fairness definitions in the original paper, 
   for reference.
 *)
(*** Proportionality ***)

(* SD proportionality - Section 4 Proportionality, (ii) (a) *)
definition 
  SD_proportionality :: "('agent, 'alt) assignment \<Rightarrow> bool"
where
  "SD_proportionality A \<equiv>
    \<forall>i \<in> agents. (A i) \<succeq>[SDA(R i)] (pmf_like_set alts)"

(* Weak SD proportionality - Section 4 Proportionality, (i) (a) *)
definition 
  weak_SD_proportionality :: "('agent, 'alt) assignment \<Rightarrow> bool"
where
  "weak_SD_proportionality A \<equiv>
    \<forall>i \<in> agents. \<not>((pmf_like_set alts) \<succ>[SDA(R i)] (A i))"

(* Possible proportionality - Section 4 Proportionality, (i) (b) *)
definition 
  possible_proportionality :: "('agent, 'alt) assignment \<Rightarrow> bool"
where
  "possible_proportionality A \<equiv>
    \<forall>i \<in> agents. \<exists>u :: ('alt \<Rightarrow> real). vnm_utility alts (R i) u \<and> 
     sum_utility u alts (A i) \<ge> sum u alts / (card agents)"

(* Necessary proportionality - Section 4 Proportionality, (ii) (b) *)
definition 
  necessary_proportionality :: "('agent, 'alt) assignment \<Rightarrow> bool"
where
  "necessary_proportionality A \<equiv>
    \<forall>i \<in> agents. \<forall>u :: ('alt \<Rightarrow> real).( vnm_utility alts (R i) u \<longrightarrow> 
      sum_utility u alts (A i)  \<ge> sum u alts / (card agents))"

(*** Envy-freeness ***)

(* SD envyfreeness - Section 4 Envyfreeness, (ii) (a)*)
definition 
  SD_envyfreeness :: "('agent, 'alt) assignment \<Rightarrow> bool"
where
  "SD_envyfreeness A \<equiv>
    \<forall>i \<in> agents. \<forall>j \<in> agents. (A i) \<succeq>[SDA(R i)] (A j)"

(* Weak SD envyfreeness - Section 4 Envyfreeness, (i) (a) *)
definition 
  weak_SD_envyfreeness :: "('agent, 'alt) assignment \<Rightarrow> bool"
where 
  "weak_SD_envyfreeness A \<equiv>
    \<forall>i \<in> agents. \<forall>j \<in> agents. \<not> ((A j) \<succ>[SDA(R i)] (A i))"

(* Possible envyfreeness - Section 4 Envyfreeness, (i) (b) *)
definition 
  possible_envyfreeness :: "('agent, 'alt) assignment \<Rightarrow> bool"
where
  "possible_envyfreeness A \<equiv>
    \<forall>i \<in> agents. \<exists>u :: ('alt \<Rightarrow> real). \<forall>j \<in> agents. vnm_utility alts (R i) u 
    \<and> sum_utility u alts (A i) \<ge> sum_utility u alts (A j)"

(* Necessary envyfreeness - Section 4 Envyfreeness, (ii) (b) *)
definition 
  necessary_envyfreeness :: "('agent, 'alt) assignment \<Rightarrow> bool"
where
  "necessary_envyfreeness A \<equiv>
    \<forall>i \<in> agents. \<forall>u :: ('alt \<Rightarrow> real). \<forall>j \<in> agents. vnm_utility alts (R i) u
    \<longrightarrow> sum_utility u alts (A i) \<ge> sum_utility u alts (A j)"
end

context discrete_assignment
begin
(* Possible completion envyfreeness - Section 4 Envyfreeness, (i) (c)
   Alternative definition   
 *)
definition 
  possible_completion_envyfreeness' :: "('agent, 'alt) assignment \<Rightarrow> bool"
where 
  "possible_completion_envyfreeness' A \<equiv>
    \<forall>i \<in> agents. (\<exists>P :: 'alt set \<Rightarrow> 'alt set \<Rightarrow> bool. 
      (\<forall>s1 s2.  s2 \<succeq>[RS(R i)] s1 \<longleftrightarrow> s2 \<succeq>[P] s1) \<and> 
    (\<forall>j \<in> agents. allocated_alts (A i) alts \<succeq>[P] allocated_alts (A j) alts))"

(* Necessary completion envyfreeness - Section 4 Envyfreeness, (ii) (c)
   Alternative definition
*)
definition 
  necessary_completion_envyfreeness' :: "('agent, 'alt) assignment \<Rightarrow> bool"
where
  "necessary_completion_envyfreeness' A \<equiv>
  \<forall>i \<in> agents. (\<forall>P :: 'alt set \<Rightarrow> 'alt set \<Rightarrow> bool. 
      (\<forall>s1 s2.  s2 \<succeq>[RS(R i)] s1 \<longleftrightarrow> s2 \<succeq>[P] s1) \<longrightarrow>
    (\<forall>j \<in> agents. allocated_alts (A i) alts \<succeq>[P] allocated_alts (A j) alts))"

(* Possible completion envyfreeness - Section 4 Envyfreeness, (i) (c) *)

definition 
  possible_completion_envyfreeness :: "('agent, 'alt) assignment \<Rightarrow> bool"
where 
  "possible_completion_envyfreeness A \<equiv>
  \<forall>i \<in> agents. (\<exists>P :: 'alt set \<Rightarrow> 'alt set \<Rightarrow> bool. 
    (\<forall>s1 s2.  s2 \<succeq>[RS(R i)] s1 \<longrightarrow> s2 \<succeq>[P] s1) \<and> 
  (\<forall>j \<in> agents. allocated_alts (A i) alts \<succeq>[P] allocated_alts (A j) alts))"



(* Necessary completion envyfreeness - Section 4 Envyfreeness, (ii) (c)*)
definition 
  necessary_completion_envyfreeness :: "('agent, 'alt) assignment \<Rightarrow> bool"
where
  "necessary_completion_envyfreeness A \<equiv>
   \<forall>i \<in> agents. (\<forall>P :: 'alt set \<Rightarrow> 'alt set \<Rightarrow> bool. 
    (\<forall>s1 s2. s2 \<succeq>[RS(R i)] s1 \<longrightarrow> s2 \<succeq>[P] s1) \<longrightarrow>
     (\<forall>j \<in> agents. allocated_alts (A i) alts \<succeq>[P] allocated_alts (A j) alts))"
end

context random_assignment
begin
lemma pair_is_pmf_like_set: 
  fixes i :: "'agent"
  assumes "i \<in> agents"
  shows "random_pair_allocation alts (p i) (pmf_like_set alts) (R i)" 
  and   "random_pair_allocation alts  (pmf_like_set alts) (p i) (R i)" 
  using assms 
   by (metis (no_types, opaque_lifting) pref_profile_wf_def random_alloc_pmf 
        random_assignment_axioms random_assignment_def random_pair_allocation_def 
sum_m_over_n sum_pmf_like_set)+
 

lemma two_random_alloc: 
  fixes k i j
  assumes "k \<in> agents"
  assumes "i \<in> agents"
  assumes "j \<in> agents"
  shows "random_pair_allocation alts (p i) (p j) (R k)"
    by (metis assms random_pair_allocation_def pair_is_pmf_like_set(1))
(*
lemma gen_two_random_alloc: "\<forall>k i j. ((k \<in> agents) \<and> (i \<in> agents) \<and> (j \<in> agents)) \<longrightarrow>
  random_pair_allocation alts (p i) (p j) (R k) "
  by (auto simp add: two_random_alloc)
*)
(* Equivalences, random *)
(* Equivalence (1) *)
theorem weak_possible_prop: 
  "possible_proportionality p = weak_SD_proportionality p"
  unfolding possible_proportionality_def weak_SD_proportionality_def  
  by (metis pair_is_pmf_like_set(1) random_pair_allocation.not_strict_SDA_utility sum_divide_agents)
  
(* Equivalence (2) *)
theorem SD_necessary_prop: "SD_proportionality p = necessary_proportionality p"
  unfolding SD_proportionality_def necessary_proportionality_def
  by (metis pair_is_pmf_like_set(1) random_pair_allocation.frac_SDA_utility sum_divide_agents)

(* Equivalence (4) first equivalence *)
theorem SD_necessary_envy: "SD_envyfreeness p = necessary_envyfreeness p"
  unfolding SD_envyfreeness_def necessary_envyfreeness_def
  by (meson random_pair_allocation.frac_SDA_utility two_random_alloc)

(* Implications, random *)
(* Implication (5) *)
theorem SD_envy_imp_SD_prop: "SD_envyfreeness p \<Longrightarrow> SD_proportionality p"
proof -
  assume "SD_envyfreeness p"
  from this SD_necessary_envy have "necessary_envyfreeness p" by simp
  from this necessary_envyfreeness_def[of "p"] have 
    env: "\<forall>i\<in>agents. \<forall>u. \<forall>j\<in>agents. vnm_utility alts (R i) u \<longrightarrow> sum_utility u alts (p j) \<le> sum_utility u alts (p i)"
    by auto
  have "necessary_proportionality p"
  proof (unfold necessary_proportionality_def, rule ballI, rule allI, rule impI)
    fix i :: "'agent" 
    fix u :: "'alt \<Rightarrow> real"
    assume iagent: "i \<in> agents"
    assume uult: "vnm_utility alts (R i) u"
    from env iagent uult have "\<forall>j \<in> agents.  sum_utility u alts (p j) \<le> sum_utility u alts (p i)" by auto
    hence sum_times: "(\<Sum>j \<in> agents. sum_utility u alts (p j)) \<le> sum_utility u alts (p i) * (card agents)" 
      by (simp add: Groups.mult_ac(2) sum_bounded_above)
    moreover from sum_utility_def have "(\<Sum>j \<in> agents. sum_utility u alts (p j)) 
      = (\<Sum>j \<in> agents. (\<Sum>i \<in> alts. u i * p j i))" 
      by metis
    moreover have "(\<Sum>j \<in> agents. (\<Sum>i \<in> alts. u i * p j i)) = (\<Sum>i \<in> alts. (\<Sum>j \<in> agents. u i * p j i))"
      using sum.swap by fastforce
    moreover from random_assignment_def have "\<forall>i \<in> alts. (\<Sum>j \<in> agents. p j i) = 1" by auto
    moreover hence "\<forall>i \<in> alts. (\<Sum>j \<in> agents. u i * p j i) = u i" 
      by (metis mult_cancel_left1 sum_distrib_left)
    ultimately have "(\<Sum>j \<in> agents. sum_utility u alts (p j)) = sum u alts" by auto
    from this sum_times have ineq: "sum u alts \<le> sum_utility u alts (p i) * real (card agents)" by auto
    from random_assignment_def have "finite agents" by auto
    from random_assignment_def pref_profile_wf_def have "agents \<noteq> {}"
      using iagent by force
    from this `finite agents` have "card agents > 0" by auto
    hence "real (card agents) > 0" by auto
    from this ineq show "sum u alts / real (card agents) \<le> sum_utility u alts (p i)" 
      using pos_divide_le_eq by blast
  qed
  from this SD_necessary_prop have "SD_proportionality p" by auto
  thus "SD_proportionality p"
    by auto
qed

corollary SD_envy_imp_necessary_prop: 
  "SD_envyfreeness p \<Longrightarrow> necessary_proportionality p"
  using SD_necessary_prop SD_envy_imp_SD_prop
  by simp

corollary necessary_envy_imp_SD_prop: 
  "necessary_envyfreeness p \<Longrightarrow> SD_proportionality p"
  using SD_necessary_envy SD_envy_imp_SD_prop
  by simp

corollary necessary_envy_imp_necessary_prop: 
  "necessary_envyfreeness p \<Longrightarrow> necessary_proportionality p"
  using SD_necessary_envy SD_envy_imp_SD_prop SD_necessary_prop
  by simp

(* Implication (6) *)
theorem SD_imp_weak_SD_prop: 
  "SD_proportionality p \<Longrightarrow> weak_SD_proportionality p"
  unfolding SD_proportionality_def weak_SD_proportionality_def
  by (simp add: strongly_preferred_def)


corollary SD_imp_possible_prop: 
  "SD_proportionality p \<Longrightarrow> possible_proportionality p"
  using SD_imp_weak_SD_prop weak_possible_prop
  by simp

corollary necessary_imp_weak_SD_prop: 
  "necessary_proportionality p \<Longrightarrow> weak_SD_proportionality p"
  using SD_necessary_prop SD_imp_weak_SD_prop
  by simp

corollary necessary_imp_possible_prop: 
  "necessary_proportionality p \<Longrightarrow> possible_proportionality p"
  using SD_necessary_prop SD_imp_weak_SD_prop weak_possible_prop
  by simp

(* Implication (9) *)
theorem necessary_envyfreeness_implies_possible_envyfreeness: 
  "necessary_envyfreeness p \<Longrightarrow> possible_envyfreeness p"
  unfolding possible_envyfreeness_def 
  using SD_imp_possible_prop necessary_envy_imp_SD_prop 
    necessary_envyfreeness_def
    possible_proportionality_def 
  by blast

corollary SD_imp_possible_envy: 
  "SD_envyfreeness p \<Longrightarrow> possible_envyfreeness p"
  using necessary_envyfreeness_implies_possible_envyfreeness SD_necessary_envy
  by simp
 
(* Implication (7) *)
theorem poss_envy_imp_weak_SD_prop: 
  "possible_envyfreeness p \<Longrightarrow> weak_SD_proportionality p"
proof -
  assume "possible_envyfreeness p"
  hence "possible_proportionality p"
  proof (unfold possible_envyfreeness_def possible_proportionality_def)
    assume allit: " \<forall>i\<in>agents.
       \<exists>u. \<forall>j\<in>agents.
              vnm_utility alts (R i) u \<and>
              sum_utility u alts (p j) \<le> sum_utility u alts (p i)"
    show divide: "\<forall>i\<in>agents.
       \<exists>u. vnm_utility alts (R i) u \<and>
           sum u alts / real (card agents) \<le> sum_utility u alts (p i)"
    proof (rule ballI)
      fix i
      assume iagent: "i \<in> agents"
      from this allit 
      have "\<exists>u. \<forall>j\<in>agents.
              vnm_utility alts (R i) u \<and>
              sum_utility u alts (p j) \<le> sum_utility u alts (p i)" by auto
      from this obtain u 
        where u_def: "\<forall>j\<in>agents. vnm_utility alts (R i) u \<and>
              sum_utility u alts (p j) \<le> sum_utility u alts (p i)" by auto
      from u_def have uult: "vnm_utility alts (R i) u"
        using iagent by blast
      from u_def have  "\<forall>j \<in> agents. sum_utility u alts (p j) \<le> sum_utility u alts (p i)" 
        by simp
      hence sum_times: "(\<Sum>j \<in> agents. sum_utility u alts (p j)) \<le> sum_utility u alts (p i) * (card agents)" 
        by (simp add: Groups.mult_ac(2) sum_bounded_above)
      moreover from sum_utility_def have "(\<Sum>j \<in> agents. sum_utility u alts (p j)) 
        = (\<Sum>j \<in> agents. (\<Sum>i \<in> alts. u i * p j i))" 
        by metis
      moreover have "(\<Sum>j \<in> agents. (\<Sum>i \<in> alts. u i * p j i)) = (\<Sum>i \<in> alts. (\<Sum>j \<in> agents. u i * p j i))"
        using sum.swap by fastforce
      moreover from random_assignment_def have "\<forall>i \<in> alts. (\<Sum>j \<in> agents. p j i) = 1" by auto
      moreover hence "\<forall>i \<in> alts. (\<Sum>j \<in> agents. u i * p j i) = u i" 
        by (metis mult_cancel_left1 sum_distrib_left)
      ultimately have "(\<Sum>j \<in> agents. sum_utility u alts (p j)) = sum u alts" by auto
      from this sum_times have ineq: "sum u alts \<le> sum_utility u alts (p i) * real (card agents)" by auto
      from random_assignment_def have "finite agents" by auto
      from random_assignment_def pref_profile_wf_def have "agents \<noteq> {}"
        using iagent by force
      from this `finite agents` have "card agents > 0" by auto
      hence "real (card agents) > 0" by auto
      from this ineq have"sum u alts / real (card agents) \<le> sum_utility u alts (p i)" 
        using pos_divide_le_eq by blast
      from this uult show "\<exists>u. vnm_utility alts (R i) u \<and> sum u alts / real (card agents) \<le> sum_utility u alts (p i)"
        by auto
    qed
  qed
  from this weak_possible_prop show "weak_SD_proportionality p" by auto
qed

(* Implication (8) *)
theorem poss_envy_imp_weak_SD_envy: "possible_envyfreeness p \<Longrightarrow> weak_SD_envyfreeness p"
  unfolding weak_SD_envyfreeness_def possible_envyfreeness_def
  using random_pair_allocation.not_strict_SDA_utility two_random_alloc 
  by blast
end

context discrete_assignment
begin



lemma two_discrete_alloc: 
  fixes k i j
  assumes "k \<in> agents"
  assumes "i \<in> agents"
  assumes "j \<in> agents"
  shows "discrete_pair_allocation alts (p i) (p j) (R k)"
  by (metis assms discrete_pair_allocation_def discr 
      discrete_pair_allocation_axioms_def two_random_alloc)

(* Equivalence, discrete *)
(* Equivalence (4), second equivalence *)
theorem SD_compl: 
  "SD_envyfreeness p = necessary_completion_envyfreeness p"
  unfolding SD_envyfreeness_def necessary_completion_envyfreeness_def 
  using discrete_pair_allocation.SDA_RS two_discrete_alloc 
  by blast

corollary necessary_envyfreeness_eq_NC_envyfreeness:
  "necessary_envyfreeness p = necessary_completion_envyfreeness p"
  using SD_compl SD_necessary_envy 
  by blast

corollary NC_implies_possible_envyfreeness:
  "necessary_completion_envyfreeness p \<Longrightarrow> possible_envyfreeness p"
  using necessary_envyfreeness_eq_NC_envyfreeness 
        necessary_envyfreeness_implies_possible_envyfreeness
  by simp

corollary NC_envy_imp_SD_prop:
  "necessary_completion_envyfreeness p \<Longrightarrow> SD_proportionality p"
  using SD_compl SD_envy_imp_SD_prop
  by simp

corollary NC_envy_imp_necessary_prop:
  "necessary_completion_envyfreeness p \<Longrightarrow> necessary_proportionality p"
  using SD_compl SD_necessary_prop SD_envy_imp_SD_prop
  by simp




(* Implication, discrete *)
(* Implication (3a) - modified from Equivalence (3) *)

theorem possible_completion_envyfreeness_trivial: 
  "possible_completion_envyfreeness p"
  unfolding possible_completion_envyfreeness_def 
  by blast

corollary poss_envy_imp_PC_envy:
  "possible_envyfreeness p \<Longrightarrow> possible_completion_envyfreeness p"
  using  possible_completion_envyfreeness_trivial
  by simp


theorem possible_completion_envyfreeness_implies_weak_SD_envyfreeness:
  "possible_completion_envyfreeness p \<longrightarrow> weak_SD_envyfreeness p"
  unfolding  weak_SD_envyfreeness_def 
  apply (insert sum_prob_equal_agents) unfolding sum_def
  (*nitpick *)
  oops
end

abbreviation
  R_example :: "bool \<Rightarrow> bool relation"
  where
  "R_example  \<equiv> \<lambda>i a1 a2. (a1 \<or>\<not>a2)" 

abbreviation 
  p_example :: "bool\<Rightarrow> bool \<Rightarrow> real"
where
  "p_example \<equiv> \<lambda>i a. if ((i\<and>\<not>a) \<or> (\<not>i\<and>a)) then 1 else 0"


abbreviation 
  P_example :: "(bool set) relation"
where
  "P_example \<equiv> \<lambda>S1 S2. True"

interpretation example_random_assignment:
  random_assignment "{True, False}" "{True, False}" R_example p_example
  by unfold_locales  (simp_all add: random_allocation_def, metis)

interpretation example_discrete_assignment: 
 discrete_assignment "{True, False}" "{True, False}" R_example p_example
  by unfold_locales (simp add: discrete_allocation.intro discrete_allocation_axioms.intro)  

lemma counter_example_possible_completion_envyfreeness_implies_weak_SD_envyfreeness_helper: 
  "example_discrete_assignment.possible_completion_envyfreeness p_example \<and> 
  (\<exists>i\<in>{True, False}. \<exists>j\<in>{True, False}. p_example i \<prec>[SDA (R_example i)] p_example j)"
  unfolding example_discrete_assignment.possible_completion_envyfreeness_def 
              SDA_def strongly_preferred_def
  apply safe
    apply (rule_tac x=P_example in exI, blast)
   apply (rule_tac x=P_example in exI, blast) 
  apply (rule_tac x=False in bexI[rotated], simp)
  apply (rule_tac x=True in bexI[rotated], simp)
  apply clarsimp
  apply(rule conjI)
   apply (rule allI)
   apply (case_tac x, simp_all add: UNIV_bool)
  apply (rule_tac x=False in exI, fastforce)
  done

theorem counter_example_possible_completion_envyfreeness''_implies_weak_SD_envyfreeness: 
  "example_discrete_assignment.possible_completion_envyfreeness p_example \<and> 
  \<not>  example_random_assignment.weak_SD_envyfreeness p_example"
  using counter_example_possible_completion_envyfreeness_implies_weak_SD_envyfreeness_helper
  unfolding example_random_assignment.weak_SD_envyfreeness_def
  by blast


abbreviation
  R_example' :: "bool \<Rightarrow> bool relation"
  where
"R_example'  \<equiv> \<lambda>i a1 a2. \<not> ((i \<and> a1 \<and> \<not>a2) \<or> (\<not>i \<and> \<not>a1 \<and> a2))"


abbreviation 
  p_example' :: "bool\<Rightarrow> bool \<Rightarrow> real"
where
  "p_example' \<equiv> \<lambda>i a. if ((i\<and>\<not>a) \<or> (\<not>i\<and>a)) then 1 else 0"

interpretation example'_random_assignment:
  random_assignment "{True, False}" "{True, False}" R_example' p_example'
  by unfold_locales (simp_all add: random_allocation_def, blast, blast)         

context discrete_assignment
begin
(* 
  Demonstration that the definition of necessary completion envyfree and possible completion envyfree
  are actually equivalent when the definition uses biimplication to define "consistent with
  the responsive set extension"
*)
lemma exist_one_relation: 
  "\<forall>i \<in> agents. \<exists>!P. (\<forall>s1 s2. (RS (R i)) s1 s2 \<longleftrightarrow> P s1 s2)" 
  by blast
lemma exactly_one_relation: 
  "\<forall>i \<in> agents. \<forall>P. ((\<forall>s1 s2. (RS (R i)) s1 s2 \<longleftrightarrow> P s1 s2) \<longleftrightarrow> P = RS (R i))"
  by blast

theorem equivalent_defs: 
  "necessary_completion_envyfreeness' p = possible_completion_envyfreeness' p"
  unfolding necessary_completion_envyfreeness'_def possible_completion_envyfreeness'_def 
  by blast


end
end