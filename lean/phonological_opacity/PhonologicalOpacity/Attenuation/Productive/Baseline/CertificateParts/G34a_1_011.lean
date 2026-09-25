import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G34a_1_010
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG34a_1_888 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɛ","ɔ","k","p","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_889 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɛ","ɔ","k","p","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_890 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɛ","ɔ","k","p","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_891 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɛ","ɔ","k","p","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_892 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɛ","ɔ","k","p","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_893 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɛ","ɔ","k","p","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_880 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɛ","ɔ","k","p"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34a_1_881
  · exact partG34a_1_882
  · exact partG34a_1_883
  · exact partG34a_1_884
  · exact partG34a_1_885
  · exact partG34a_1_886
  · exact partG34a_1_887
  · exact partG34a_1_888
  · exact partG34a_1_889
  · exact partG34a_1_890
  · exact partG34a_1_891
  · exact partG34a_1_892
  · exact partG34a_1_893
theorem partG34a_1_879 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɛ","ɔ","k"] [["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="p" := by simpa using hx
  subst x
  exact partG34a_1_880
theorem partG34a_1_878 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɛ","ɔ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="k" := by simpa using hx
  subst x
  exact partG34a_1_879
theorem partG34a_1_894 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɛ","o"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_895 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɛ","ʊ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_896 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɛ","u"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_897 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɛ","j"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_898 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɛ","w"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_870 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34a_1_871
  · exact partG34a_1_872
  · exact partG34a_1_873
  · exact partG34a_1_874
  · exact partG34a_1_875
  · exact partG34a_1_876
  · exact partG34a_1_877
  · exact partG34a_1_878
  · exact partG34a_1_894
  · exact partG34a_1_895
  · exact partG34a_1_896
  · exact partG34a_1_897
  · exact partG34a_1_898
theorem partG34a_1_903 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","∅","k","p","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_904 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","∅","k","p","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_905 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","∅","k","p","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_906 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","∅","k","p","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_907 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","∅","k","p","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_908 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","∅","k","p","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_909 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","∅","k","p","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_910 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","∅","k","p","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_911 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","∅","k","p","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_912 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","∅","k","p","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_913 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","∅","k","p","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_914 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","∅","k","p","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_915 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","∅","k","p","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_902 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","∅","k","p"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34a_1_903
  · exact partG34a_1_904
  · exact partG34a_1_905
  · exact partG34a_1_906
  · exact partG34a_1_907
  · exact partG34a_1_908
  · exact partG34a_1_909
  · exact partG34a_1_910
  · exact partG34a_1_911
  · exact partG34a_1_912
  · exact partG34a_1_913
  · exact partG34a_1_914
  · exact partG34a_1_915
theorem partG34a_1_901 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","∅","k"] [["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="p" := by simpa using hx
  subst x
  exact partG34a_1_902
theorem partG34a_1_900 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","∅"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="k" := by simpa using hx
  subst x
  exact partG34a_1_901
theorem partG34a_1_916 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","a"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_917 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","ɜ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_918 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","ɛ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_919 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","e"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_920 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","ɪ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_921 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","i"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_925 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","ɔ","k","p","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_926 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","ɔ","k","p","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_927 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","ɔ","k","p","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_928 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","ɔ","k","p","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_929 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","ɔ","k","p","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_930 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","ɔ","k","p","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_931 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","ɔ","k","p","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_932 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","ɔ","k","p","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_933 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","ɔ","k","p","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_934 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","ɔ","k","p","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_935 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","ɔ","k","p","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_936 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","ɔ","k","p","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_937 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","ɔ","k","p","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_924 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","ɔ","k","p"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34a_1_925
  · exact partG34a_1_926
  · exact partG34a_1_927
  · exact partG34a_1_928
  · exact partG34a_1_929
  · exact partG34a_1_930
  · exact partG34a_1_931
  · exact partG34a_1_932
  · exact partG34a_1_933
  · exact partG34a_1_934
  · exact partG34a_1_935
  · exact partG34a_1_936
  · exact partG34a_1_937
theorem partG34a_1_923 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","ɔ","k"] [["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="p" := by simpa using hx
  subst x
  exact partG34a_1_924
theorem partG34a_1_922 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","ɔ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="k" := by simpa using hx
  subst x
  exact partG34a_1_923
theorem partG34a_1_938 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","o"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_939 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","ʊ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_940 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","u"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_941 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","j"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_942 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e","w"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_899 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34a_1_900
  · exact partG34a_1_916
  · exact partG34a_1_917
  · exact partG34a_1_918
  · exact partG34a_1_919
  · exact partG34a_1_920
  · exact partG34a_1_921
  · exact partG34a_1_922
  · exact partG34a_1_938
  · exact partG34a_1_939
  · exact partG34a_1_940
  · exact partG34a_1_941
  · exact partG34a_1_942
theorem partG34a_1_944 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɪ","∅"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_945 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɪ","a"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_946 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɪ","ɜ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_947 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɪ","ɛ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_948 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɪ","e"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_949 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɪ","ɪ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_950 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɪ","i"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_954 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɪ","ɔ","k","p","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_955 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɪ","ɔ","k","p","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_956 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɪ","ɔ","k","p","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_957 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɪ","ɔ","k","p","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_958 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɪ","ɔ","k","p","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_959 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɪ","ɔ","k","p","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_960 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɪ","ɔ","k","p","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_961 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɪ","ɔ","k","p","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_962 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɪ","ɔ","k","p","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_963 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɪ","ɔ","k","p","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_964 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɪ","ɔ","k","p","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_965 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɪ","ɔ","k","p","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_966 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɪ","ɔ","k","p","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_953 : check uG34a (3) (-2) outG34a ["a","h","ɛ","t","ɪ","ɔ","k","p"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34a_1_954
  · exact partG34a_1_955
  · exact partG34a_1_956
  · exact partG34a_1_957
  · exact partG34a_1_958
  · exact partG34a_1_959
  · exact partG34a_1_960
  · exact partG34a_1_961
  · exact partG34a_1_962
  · exact partG34a_1_963
  · exact partG34a_1_964
  · exact partG34a_1_965
  · exact partG34a_1_966
end ProductiveGua
