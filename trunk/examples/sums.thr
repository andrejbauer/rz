theory Sums =
thy

set s

const a : s
const b : s
const c : s

set sum = `yes : s + `no : 1 + `maybe

const (tmp : sum) = `yes a

const (d : s * 1) = 
  match tmp with
     `yes (q : s) -> (q, ())
   | `no (r : 1) -> (c, r)
   | `maybe -> (a, ())
  end


const (e : s) = d.0   # changed projection syntax since
                      # HASH was being used for comments

end
