theory Continuum imports "HOL-Analysis.Continuum_Not_Denumerable" begin

text \<open>
  Denumerable: Capable of being assigned numbers from the natural numbers.

  The empty set is denumerable because it is finite; the rational numbers are, surprisingly,
  denumerable because every possible fraction can be assigned a number.

  Synonym: Countable

  \<^url>\<open>https://en.wiktionary.org/wiki/denumerable\<close>
\<close>

proposition \<open>\<exists>f. \<forall>y :: nat. \<exists>x :: nat. y = f x\<close>
  by iprover

definition triangle :: \<open>nat \<Rightarrow> nat\<close>
  where \<open>triangle n \<equiv> (n * Suc n) div 2\<close>

lemma triangle_0 [simp]: \<open>triangle 0 = 0\<close>
  unfolding triangle_def by simp

lemma triangle_Suc [simp]: \<open>triangle (Suc n) = triangle n + Suc n\<close>
  unfolding triangle_def by simp

definition prod_encode :: \<open>nat \<times> nat \<Rightarrow> nat\<close>
  where \<open>prod_encode \<equiv> \<lambda>(m, n). triangle (m + n) + m\<close>

fun prod_decode_aux :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat\<close>
  where \<open>prod_decode_aux k m = (if k \<ge> m then (m, k - m) else prod_decode_aux (Suc k) (m - Suc k))\<close>

definition prod_decode :: \<open>nat \<Rightarrow> nat \<times> nat\<close>
  where \<open>prod_decode \<equiv> prod_decode_aux 0\<close>

lemma prod_decode_triangle_add: \<open>prod_decode (triangle k + m) = prod_decode_aux k m\<close>
  unfolding prod_decode_def
  by (induct k arbitrary: m) (simp, simp only: triangle_Suc add.assoc, simp)

lemma prod_encode_inverse [simp]: \<open>prod_decode (prod_encode x) = x\<close>
  unfolding prod_encode_def using prod_decode_triangle_add by (cases x) simp

lemma prod_encode_prod_decode_aux: \<open>prod_encode (prod_decode_aux k m) = triangle k + m\<close>
  unfolding prod_encode_def by (induct k m rule: prod_decode_aux.induct) simp

lemma prod_decode_inverse [simp]: \<open>prod_encode (prod_decode n) = n\<close>
  unfolding prod_decode_def by (simp add: prod_encode_prod_decode_aux del: prod_decode_aux.simps)

definition sum_encode :: \<open>nat + nat \<Rightarrow> nat\<close>
  where \<open>sum_encode x \<equiv> case x of Inl a \<Rightarrow> 2 * a | Inr b \<Rightarrow> Suc (2 * b)\<close>

definition sum_decode :: \<open>nat \<Rightarrow> nat + nat\<close>
  where \<open>sum_decode n \<equiv> if even n then Inl (n div 2) else Inr (n div 2)\<close>

lemma sum_encode_inverse [simp]: \<open>sum_decode (sum_encode x) = x\<close>
  unfolding sum_encode_def sum_decode_def by (cases x) simp_all

lemma sum_decode_inverse [simp]: \<open>sum_encode (sum_decode n) = n\<close>
  unfolding sum_encode_def sum_decode_def by simp

definition int_encode :: \<open>int \<Rightarrow> nat\<close>
  where \<open>int_encode i \<equiv> sum_encode (if i \<ge> 0 then Inl (nat i) else Inr (nat (- i - 1)))\<close>

definition int_decode :: \<open>nat \<Rightarrow> int\<close>
  where \<open>int_decode n \<equiv> case sum_decode n of Inl a \<Rightarrow> int a | Inr b \<Rightarrow> - int b - 1\<close>

lemma int_encode_inverse [simp]: \<open>int_decode (int_encode x) = x\<close>
  unfolding int_encode_def int_decode_def by simp

lemma int_decode_inverse [simp]: \<open>int_encode (int_decode n) = n\<close>
  unfolding int_encode_def int_decode_def unfolding sum_encode_def sum_decode_def by simp

theorem int_denum: \<open>\<exists>f :: nat \<Rightarrow> int. surj f\<close>
  unfolding surj_def using int_encode_inverse by metis

corollary \<open>\<exists>f. \<forall>y :: int. \<exists>x :: nat. y = f x\<close>
  using int_denum unfolding surj_def .

definition nat_to_rat_surj :: \<open>nat \<Rightarrow> rat\<close>
  where \<open>nat_to_rat_surj n \<equiv> let (a, b) = prod_decode n in Fract (int_decode a) (int_decode b)\<close>

lemma surj_nat_to_rat_surj: \<open>surj nat_to_rat_surj\<close>
  unfolding surj_def nat_to_rat_surj_def
  using Rat_cases case_prod_conv int_encode_inverse prod_encode_inverse by metis

theorem rat_denum: \<open>\<exists>f :: nat \<Rightarrow> rat. surj f\<close>
  using surj_nat_to_rat_surj by metis

corollary \<open>\<exists>f. \<forall>y :: rat. \<exists>x :: nat. y = f x\<close>
  using rat_denum unfolding surj_def .

text \<open>
  Examples of nondenumerable sets include the real, complex, irrational, and transcendental
  numbers.

  \<^url>\<open>http://mathworld.wolfram.com/CountablyInfinite.html\<close>
\<close>

proposition \<open>\<nexists>f. \<forall>y :: real. \<exists>x :: nat. y = f x\<close>
  using real_non_denum unfolding surj_def .

end
