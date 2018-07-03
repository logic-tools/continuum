theory Proof imports Complex_Main
begin

theorem \<open>\<nexists>f :: nat \<Rightarrow> real. surj f\<close>
proof
  assume \<open>\<exists>f :: nat \<Rightarrow> real. surj f\<close>
  show False
  proof -
    from \<open>\<exists>f. surj f\<close> obtain f :: \<open>nat \<Rightarrow> real\<close> where \<open>surj f\<close> ..

    then have assumption: \<open>\<exists>n. f n = z\<close> for z
      \<proof>

    obtain D :: \<open>nat \<Rightarrow> real set\<close> where \<open>(\<Inter>n. D n) \<noteq> {}\<close> \<open>f n \<notin> D n\<close> for n
    proof -
      obtain L R :: \<open>real \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real\<close>
        where
          *: \<open>L a b c < R a b c\<close> \<open>{L a b c .. R a b c} \<subseteq> {a .. b}\<close> \<open>c \<notin> {L a b c .. R a b c}\<close>
        if \<open>a < b\<close> for a b c
      proof -
        have \<open>\<exists>x y. a \<le> x \<and> x < y \<and> y \<le> b \<and> \<not> (x \<le> c \<and> c \<le> y)\<close> if \<open>a < b\<close> for a b c :: real
          \<proof>

        then have \<open>\<exists>x y. x < y \<and> {x .. y} \<subseteq> {a .. b} \<and> c \<notin> {x .. y}\<close> if \<open>a < b\<close> for a b c :: real
          \<proof>

        then show ?thesis
          \<proof>
      qed

      define P :: \<open>nat \<Rightarrow> real \<times> real\<close>
        where
          \<open>P \<equiv> rec_nat
               (L 0 1 (f 0),
                R 0 1 (f 0))
               (\<lambda>n (x, y). (L x y (f (Suc n)),
                            R x y (f (Suc n))))\<close>

      with *(1) have 0: \<open>fst (P n) < snd (P n)\<close> for n
        \<proof>

      define I :: \<open>nat \<Rightarrow> real set\<close>
        where
          \<open>I \<equiv> \<lambda>n. {fst (P n) .. snd (P n)}\<close>

      with 0 have \<open>I n \<noteq> {}\<close> for n
        \<proof>

      moreover from 0 *(2) have \<open>decseq I\<close>
        \<proof>

      ultimately have \<open>finite S \<longrightarrow> (\<Inter>n\<in>S. I n) \<noteq> {}\<close> for S
        \<proof>

      moreover have \<open>closed (I n)\<close> for n
        \<proof>

      moreover have \<open>compact (I n)\<close> for n
        \<proof>

      ultimately have \<open>(\<Inter>n. I n) \<noteq> {}\<close>
        \<proof>

      moreover from 0 *(3) have \<open>f n \<notin> I n\<close> for n
        \<proof>

      ultimately show ?thesis ..
    qed

    then obtain e where \<open>\<nexists>n. f n = e\<close>
      \<proof>

    moreover from assumption have \<open>\<exists>n. f n = e\<close> .

    ultimately show ?thesis ..
  qed
qed

end \<comment> \<open>Jørgen Villadsen, DTU Denmark - Based on work by Benjamin Porter, NICTA Australia\<close>
