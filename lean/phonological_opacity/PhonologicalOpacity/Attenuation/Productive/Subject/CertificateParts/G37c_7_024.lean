import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_023
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_1927 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1928 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1929 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1916 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1917
  · exact partG37c_7_1918
  · exact partG37c_7_1919
  · exact partG37c_7_1920
  · exact partG37c_7_1921
  · exact partG37c_7_1922
  · exact partG37c_7_1923
  · exact partG37c_7_1924
  · exact partG37c_7_1925
  · exact partG37c_7_1926
  · exact partG37c_7_1927
  · exact partG37c_7_1928
  · exact partG37c_7_1929
theorem partG37c_7_1915 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_1916
theorem partG37c_7_1930 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1931 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1932 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1933 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1934 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1937 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1938 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1939 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1940 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1941 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1942 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1943 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1944 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1945 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1946 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1947 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1948 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1949 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1936 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1937
  · exact partG37c_7_1938
  · exact partG37c_7_1939
  · exact partG37c_7_1940
  · exact partG37c_7_1941
  · exact partG37c_7_1942
  · exact partG37c_7_1943
  · exact partG37c_7_1944
  · exact partG37c_7_1945
  · exact partG37c_7_1946
  · exact partG37c_7_1947
  · exact partG37c_7_1948
  · exact partG37c_7_1949
theorem partG37c_7_1935 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_1936
theorem partG37c_7_1950 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1951 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1952 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1953 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1956 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1957 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1958 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1959 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1960 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1961 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1962 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1963 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1964 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1965 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1966 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1967 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1968 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1955 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1956
  · exact partG37c_7_1957
  · exact partG37c_7_1958
  · exact partG37c_7_1959
  · exact partG37c_7_1960
  · exact partG37c_7_1961
  · exact partG37c_7_1962
  · exact partG37c_7_1963
  · exact partG37c_7_1964
  · exact partG37c_7_1965
  · exact partG37c_7_1966
  · exact partG37c_7_1967
  · exact partG37c_7_1968
theorem partG37c_7_1954 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_1955
theorem partG37c_7_1969 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1914 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1915
  · exact partG37c_7_1930
  · exact partG37c_7_1931
  · exact partG37c_7_1932
  · exact partG37c_7_1933
  · exact partG37c_7_1934
  · exact partG37c_7_1935
  · exact partG37c_7_1950
  · exact partG37c_7_1951
  · exact partG37c_7_1952
  · exact partG37c_7_1953
  · exact partG37c_7_1954
  · exact partG37c_7_1969
theorem partG37c_7_1973 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1974 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1975 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1976 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1977 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1978 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1979 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1980 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1981 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1982 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1983 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1984 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1985 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1972 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1973
  · exact partG37c_7_1974
  · exact partG37c_7_1975
  · exact partG37c_7_1976
  · exact partG37c_7_1977
  · exact partG37c_7_1978
  · exact partG37c_7_1979
  · exact partG37c_7_1980
  · exact partG37c_7_1981
  · exact partG37c_7_1982
  · exact partG37c_7_1983
  · exact partG37c_7_1984
  · exact partG37c_7_1985
theorem partG37c_7_1971 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_1972
theorem partG37c_7_1986 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1987 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1988 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1989 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1990 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1993 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1994 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1995 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1996 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1997 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1998 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1999 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2000 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2001 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2002 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2003 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2004 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2005 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1992 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","e","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1993
  · exact partG37c_7_1994
  · exact partG37c_7_1995
  · exact partG37c_7_1996
  · exact partG37c_7_1997
  · exact partG37c_7_1998
  · exact partG37c_7_1999
  · exact partG37c_7_2000
  · exact partG37c_7_2001
  · exact partG37c_7_2002
  · exact partG37c_7_2003
  · exact partG37c_7_2004
  · exact partG37c_7_2005
end ProductiveSubjectGua
