import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G34b_1_023
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG34b_1_1927 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","∅","o","h","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1928 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","∅","o","h","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1929 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","∅","o","h","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1930 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","∅","o","h","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1931 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","∅","o","h","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1932 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","∅","o","h","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1933 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","∅","o","h","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1934 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","∅","o","h","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1935 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","∅","o","h","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1922 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","∅","o","h"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_1923
  · exact partG34b_1_1924
  · exact partG34b_1_1925
  · exact partG34b_1_1926
  · exact partG34b_1_1927
  · exact partG34b_1_1928
  · exact partG34b_1_1929
  · exact partG34b_1_1930
  · exact partG34b_1_1931
  · exact partG34b_1_1932
  · exact partG34b_1_1933
  · exact partG34b_1_1934
  · exact partG34b_1_1935
theorem partG34b_1_1921 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","∅","o"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="h" := by simpa using hx
  subst x
  exact partG34b_1_1922
theorem partG34b_1_1936 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","∅","ʊ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1937 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","∅","u"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1938 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","∅","j"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1939 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","∅","w"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1912 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_1913
  · exact partG34b_1_1914
  · exact partG34b_1_1915
  · exact partG34b_1_1916
  · exact partG34b_1_1917
  · exact partG34b_1_1918
  · exact partG34b_1_1919
  · exact partG34b_1_1920
  · exact partG34b_1_1921
  · exact partG34b_1_1936
  · exact partG34b_1_1937
  · exact partG34b_1_1938
  · exact partG34b_1_1939
theorem partG34b_1_1943 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","∅","h","∅"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1944 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","∅","h","a"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1945 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","∅","h","ɜ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1946 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","∅","h","ɛ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1947 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","∅","h","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1948 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","∅","h","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1949 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","∅","h","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1950 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","∅","h","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1951 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","∅","h","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1952 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","∅","h","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1953 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","∅","h","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1954 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","∅","h","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1955 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","∅","h","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1942 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","∅","h"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_1943
  · exact partG34b_1_1944
  · exact partG34b_1_1945
  · exact partG34b_1_1946
  · exact partG34b_1_1947
  · exact partG34b_1_1948
  · exact partG34b_1_1949
  · exact partG34b_1_1950
  · exact partG34b_1_1951
  · exact partG34b_1_1952
  · exact partG34b_1_1953
  · exact partG34b_1_1954
  · exact partG34b_1_1955
theorem partG34b_1_1941 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","∅"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="h" := by simpa using hx
  subst x
  exact partG34b_1_1942
theorem partG34b_1_1956 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","a"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1957 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","ɜ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1958 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","ɛ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1959 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","e"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1960 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","ɪ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1961 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","i"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1962 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","ɔ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1965 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","o","h","∅"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1966 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","o","h","a"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1967 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","o","h","ɜ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1968 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","o","h","ɛ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1969 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","o","h","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1970 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","o","h","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1971 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","o","h","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1972 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","o","h","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1973 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","o","h","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1974 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","o","h","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1975 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","o","h","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1976 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","o","h","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1977 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","o","h","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1964 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","o","h"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_1965
  · exact partG34b_1_1966
  · exact partG34b_1_1967
  · exact partG34b_1_1968
  · exact partG34b_1_1969
  · exact partG34b_1_1970
  · exact partG34b_1_1971
  · exact partG34b_1_1972
  · exact partG34b_1_1973
  · exact partG34b_1_1974
  · exact partG34b_1_1975
  · exact partG34b_1_1976
  · exact partG34b_1_1977
theorem partG34b_1_1963 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","o"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="h" := by simpa using hx
  subst x
  exact partG34b_1_1964
theorem partG34b_1_1978 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","ʊ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1979 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","u"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1980 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","j"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1981 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a","w"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1940 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_1941
  · exact partG34b_1_1956
  · exact partG34b_1_1957
  · exact partG34b_1_1958
  · exact partG34b_1_1959
  · exact partG34b_1_1960
  · exact partG34b_1_1961
  · exact partG34b_1_1962
  · exact partG34b_1_1963
  · exact partG34b_1_1978
  · exact partG34b_1_1979
  · exact partG34b_1_1980
  · exact partG34b_1_1981
theorem partG34b_1_1983 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɜ","∅"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1984 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɜ","a"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1985 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɜ","ɜ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1986 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɜ","ɛ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1987 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɜ","e"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1988 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɜ","ɪ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1989 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɜ","i"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1990 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɜ","ɔ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1993 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɜ","o","h","∅"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1994 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɜ","o","h","a"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1995 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɜ","o","h","ɜ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1996 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɜ","o","h","ɛ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1997 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɜ","o","h","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1998 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɜ","o","h","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1999 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɜ","o","h","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2000 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɜ","o","h","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2001 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɜ","o","h","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2002 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɜ","o","h","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2003 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɜ","o","h","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2004 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɜ","o","h","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2005 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɜ","o","h","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1992 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɜ","o","h"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_1993
  · exact partG34b_1_1994
  · exact partG34b_1_1995
  · exact partG34b_1_1996
  · exact partG34b_1_1997
  · exact partG34b_1_1998
  · exact partG34b_1_1999
  · exact partG34b_1_2000
  · exact partG34b_1_2001
  · exact partG34b_1_2002
  · exact partG34b_1_2003
  · exact partG34b_1_2004
  · exact partG34b_1_2005
end ProductiveGua
