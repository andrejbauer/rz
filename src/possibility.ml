module L = Logic

type 'a possibility =
      YesIf of 'a * L.proposition list
    | NoBecause of string list


  
let definitely x = YesIf(x, [])

let definitelyNot s = NoBecause [s]


let possCase poss yesFn noFn =
  match poss with
      YesIf(x,req) -> 
	let (x',req') = yesFn(x,req) in YesIf (x', req')
    | NoBecause rsns -> NoBecause (noFn rsns)

let possCase' poss yesFn noFn =
  match poss with
      YesIf(x,req)   -> yesFn(x, req)
    | NoBecause rsns -> noFn rsns

let addReqs poss reqs' =
  match poss with
      YesIf(x, reqs) -> YesIf(x, reqs @ reqs')
    | NoBecause _ as answer -> answer

let ifNotWhyNot poss rsn = 
  match poss with
    (YesIf _) as answer  -> answer
  | NoBecause rsns -> NoBecause (rsn :: rsns)



let modifyIfYes modifyFn poss =
  match poss with
      YesIf(x,req) -> YesIf (modifyFn x, req)
    | NoBecause _ as answer -> answer
