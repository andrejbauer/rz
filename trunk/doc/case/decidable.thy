theory DecidableSet = thy
  set s
  axiom decidable (x:s) (y:s)  =  (x = y) or not (x = y)
end