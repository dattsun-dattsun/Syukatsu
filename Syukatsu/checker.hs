import qualified Data.Set as S


---------------------------------------------------------------
--人間の記法に近いproof checkerです。                            --
--入出力は実装してません。好きな方法で実装してください。               --
--命題論理を完全に再現したわけではありません。                       --
--自作できると確信したかったため、簡単なトイモデルを作ったということです。--
--特殊なライブラリを用いていないので、環境に左右されにくいと思います。    --
--用途に合わせ、好きに論理の公理を追加してください。                   --
--メインプログラムは90行あたりのproofCheckです。                    --
--具体例は一番下に3つ載せています。                                 --
-----------------------------------------------------------------


----------------------
--数学に必要な型の定義。--
----------------------
data Proposition  
  = Prop [Char]
  | Proposition :/\: Proposition 
  | Proposition :\/: Proposition
  | Proposition :==>: Proposition
  | ZFC `In` ZFC
  | ZFC `Subset` ZFC
  | Forall ZFC Proposition
  | Exists ZFC Proposition
  deriving (Eq, Show)
--命題です

data ZFC
  = ZFC [Char]
  | ZFC `Cup` ZFC
  | ZFC `Cap` ZFC
  | ZFC `Bigcup` ZFC
  | Power ZFC
  | Map ZFC ZFC
  deriving (Eq, Show)
--集合です

type Facts = [Proposition]

type Proof
  = (Assume, Have, Use, By)
--(仮定する命題たち, 示される命題, 使った以前示したもの, 推論規則)です

data Assume
  = Assume [Proposition]
  deriving (Show)

data Have
  = Have Proposition
  deriving (Show)

data Use
  = Use [Int]
  deriving (Show)

data By
  = By Deduction

type Deduction
  = [(Assume, Have)] -> (Assume, Have) -> Bool 
--[(仮定1, 仮定1の結論1) , (仮定2, 仮定2の結論2) ,(仮定3, 仮定3の結論3) ] が与えられた時に (仮定,仮定からの主張)を得るというのが正しいかをチェックする


takeAssume :: Proof -> [Proposition]
takeAssume (Assume xs , _ , _ , _ ) = xs

takeHave :: Proof -> Proposition
takeHave ( _ , Have x , _ , _ ) = x

takeAssumeHave :: Proof -> (Assume, Have)
takeAssumeHave ( a , b , _ , _ ) = (a,b)

takeUse :: Proof -> [Int]
takeUse ( _ , _ , Use x , _ ) = x

takeBy :: Proof -> Deduction
takeBy ( _ , _ , _ , By s ) = s

delete :: Eq a => a -> [a] -> [a]
delete x xs = filter (/= x) xs
-- xsの要素からxをすべて取り除く




---------------------------------------
--以下のproofCheckがメインプログラムです。--
---------------------------------------
proofCheck :: (Int -> Proof) -> Int -> Bool
proofCheck lem n = deduct assumehaves assumehave where 
  deduct      = takeBy $ lem n
  assumehaves = map (takeAssumeHave.lem) (takeUse (lem n) )
  assumehave  = takeAssumeHave $ lem n






----------------------------------------------------------------
--以下は推論規則です。ご自身の好きな論理の仮定を記述してください。       --
--爆発律など未実装なものもたくさんあるので、必要に応じて追加してください。--
---------------------------------------------------------------
emptyDeduct :: Deduction
emptyDeduct [] ((Assume facts), (Have conclusion ))
  | conclusion `elem` facts = True
  --結論が仮定にあればTrue
  | null [ x | x <- facts, (x :==>: conclusion) `elem` facts] == False = True
  --[a,b,b==>c] |- c はTrue
emptyDeduct [] ((Assume facts), (Have (a :/\: b) ))
  | (a `elem` facts ) && (b `elem` facts ) = True
  --[a,b,c,d] |- a /\ b はTrue
emptyDeduct [] ((Assume facts), (Have (a :\/: b) ))
  | (a `elem` facts ) || (b `elem` facts ) = True
  --[a,c,d] |- a \/ b はTrue、[a,b,d] |- a \/ b はTrue
  | otherwise = False



andAssumption :: Proposition -> Proposition -> Deduction
andAssumption s t = go where 
  go [((Assume a_s) , (Have b))] ((Assume x_s) , (Have y)) 
   | b == y && null [d | d <- (delete t (delete s a_s)), d `notElem` x_s  ] && (s :/\: t) `elem` x_s = True 
   | otherwise = False
--[([a,b,c,d] |- p)] から, [a/\b,c,d] |- p を結論付ける



orAdd :: Proposition -> Deduction
orAdd s = go where 
  go [((Assume a_s) , (Have b))] ((Assume x_s) , (Have y)) 
   | y == (s :\/: b) && a_s == x_s = True
   | y == (b :\/: s) && a_s == x_s = True
   | otherwise = False
--[([a,b,c,d] |- p)] から, [a,b,c,d] |- p\/s を結論付ける



sameAssumption :: Deduction
sameAssumption = go where 
  go [((Assume a_s) , (Have b)), ((Assume c_s) , (Have d))] ((Assume x_s) , (Have y)) 
   | a_s==c_s && c_s==x_s &&  (y == (b :/\: d)) = True
   | a_s==c_s && c_s==x_s &&  (y == (d :/\: b)) = True
   | otherwise = False
--[([a,b] |- p), ([a,b] |- q)] から, [a,b] |- p /\ q を結論付ける



sameConclusion :: Proposition -> Proposition -> Deduction
sameConclusion s t = go where 
  go [((Assume a_s) , (Have b)), ((Assume c_s) , (Have d))] ((Assume x_s) , (Have y)) 
   | b==d && d==y &&  (s `elem` a_s) && (t `elem` c_s) && ((s:\/:t) `elem` x_s ) && ( (delete s a_s) == (delete t c_s)) &&  ( (delete s a_s) == (delete (s:\/:t) x_s)) = True
   | otherwise = False
--[([a,b] |- p), ([a,c] |- p)] から, [a,b\/c] |- p を結論付ける



orConclusion :: Proposition -> Proposition -> Deduction
orConclusion s t = go where 
  go [((Assume a_s) , (Have b)), ((Assume c_s) , (Have d))] ((Assume x_s) , (Have y)) 
   | (b :\/: d) == y && a_s == [s] && c_s == [t] && x_s == [(s :\/: t)] = True 
   | otherwise = False
--[([a] |- p), ([b] |- q)] から, [ (a\/b) ] |- (p \/ q)  を結論付ける



implyDeduct :: Deduction
implyDeduct [((Assume facts1), (Have conclusion))] ((Assume facts2), (Have (a :==>: b)))
  | conclusion == b && a `elem` facts1 && null [ x | x <- facts1 , x `notElem` (a:facts2 )] = True
  | otherwise = False 
implyDeduct _ _ = False
--a ∈ facts1　かつ facts1 ⊆ ({a} ∪ facts2) のときTrue




-----------------------------------
--具体例です。それぞれ一番下が結論です。--
-----------------------------------


lemma1 :: Int -> Proof
lemma1 0 = (Assume [Prop "a" , Prop "a" :==>: Prop "b"], Have (Prop "b"), Use [], By emptyDeduct)
lemma1 1 = (Assume [Prop "a" :/\: (Prop "a" :==>: Prop "b")], Have (Prop "b") , Use [0], By (andAssumption (Prop "a") (Prop "a" :==>: Prop "b")))
lemma1 2 = (Assume [], Have ((Prop "a" :/\: (Prop "a" :==>: Prop "b")) :==>: Prop "b"), Use [1], By implyDeduct)
--modusponenceの証明
--最終行から ( a /\ (a ==> b)) ==> b が証明された。

--proofCheck lemma1 0
--proofCheck lemma1 1
--proofCheck lemma1 2
--を実行するといずれもTrueなので、この証明は正しい。

lemma2 :: Int -> Proof
lemma2 0 = (Assume [Prop "a" , Prop "b"], Have (Prop "a" :/\: Prop "b"), Use [], By emptyDeduct)
lemma2 1 = (Assume [Prop "a" , Prop "b"], Have ((Prop "a" :/\: Prop "b") :\/: (Prop "a" :/\: Prop "c")), Use [0], By (orAdd (Prop "a" :/\: Prop "c") ))
lemma2 2 = (Assume [Prop "a" , Prop "c"], Have (Prop "a" :/\: Prop "c"), Use [], By emptyDeduct)
lemma2 3 = (Assume [Prop "a" , Prop "c"], Have ((Prop "a" :/\: Prop "b") :\/: (Prop "a" :/\: Prop "c")), Use [2], By (orAdd (Prop "a" :/\: Prop "b")) )
lemma2 4 = (Assume [Prop "a" , Prop "b" :\/: Prop "c"], Have ((Prop "a" :/\: Prop "b") :\/: (Prop "a" :/\: Prop "c")), Use [1,3], By (sameConclusion (Prop "b") (Prop "c")))
lemma2 5 = (Assume [(Prop "a") :/\: (Prop "b" :\/: Prop "c")], Have ((Prop "a" :/\: Prop "b") :\/: (Prop "a" :/\: Prop "c")), Use [4], By (andAssumption (Prop "a") (Prop "b" :\/: Prop "c")))
lemma2 6 = (Assume [], Have ((Prop "a" :/\: (Prop "b" :\/: Prop "c")):==>: ((Prop "a" :/\: Prop "b") :\/: (Prop "a" :/\: Prop "c"))), Use [5], By implyDeduct)
--ド・モルガンの片方向きの証明
--最終行から (a /\ (b \/ c))　==> ((a /\ b) \/ (a /\ c)) が証明された。
--やってみた人はわかりますが、ド・モルガンの証明は案外難しいです。

--proofCheck lemma2 0
--proofCheck lemma2 1
--proofCheck lemma2 2
--proofCheck lemma2 3
--proofCheck lemma2 4
--proofCheck lemma2 5
--proofCheck lemma2 6
--を実行するといずれもTrueなので、この証明は正しい。

lemma3 :: Int -> Proof
lemma3 0 = (Assume [Prop "a" , Prop "b"], Have (Prop "b"), Use [], By emptyDeduct)
lemma3 1 = (Assume [Prop "a" :/\: Prop "b"], Have (Prop "b"), Use [0], By (andAssumption (Prop "a") (Prop "b")))
lemma3 2 = (Assume [Prop "a" , Prop "c"], Have (Prop "c"), Use [], By emptyDeduct)
lemma3 3 = (Assume [Prop "a" :/\: Prop "c"], Have (Prop "c"), Use [2], By (andAssumption (Prop "a") (Prop "c")))
lemma3 4 = (Assume [(Prop "a" :/\: Prop "b") :\/: (Prop "a" :/\: Prop "c")], Have (Prop "b" :\/: Prop "c"), Use [1,3], By (orConclusion  (Prop "a" :/\: Prop "b") (Prop "a" :/\: Prop "c") ))
lemma3 5 = (Assume [Prop "a" , Prop "b"], Have (Prop "a"), Use [], By emptyDeduct)
lemma3 6 = (Assume [Prop "a" :/\: Prop "b"], Have (Prop "a"), Use [5], By (andAssumption (Prop "a") (Prop "b")))
lemma3 7 = (Assume [Prop "a" , Prop "c"], Have (Prop "a"), Use [], By emptyDeduct)
lemma3 8 = (Assume [Prop "a" :/\: Prop "c"], Have (Prop "a"), Use [7], By (andAssumption (Prop "a") (Prop "c")))
lemma3 9 = (Assume [(Prop "a" :/\: Prop "b") :\/: (Prop "a" :/\: Prop "c")], Have (Prop "a"), Use [6,8], By (sameConclusion  (Prop "a" :/\: Prop "b") (Prop "a" :/\: Prop "c") ) )
lemma3 10 = (Assume [(Prop "a" :/\: Prop "b") :\/: (Prop "a" :/\: Prop "c")], Have (Prop "a" :/\: (Prop "b" :\/: Prop "c")), Use [4,9], By sameAssumption)
lemma3 11 = (Assume [], Have (((Prop "a" :/\: Prop "b") :\/: (Prop "a" :/\: Prop "c")) :==>: (Prop "a" :/\: (Prop "b" :\/: Prop "c"))), Use [10], By implyDeduct)
--ド・モルガンの残るもう片方向きの証明
--最終行から ((a /\ b) \/ (a /\ c)) ==> (a /\ (b \/ c)) が証明された。
--やってみた人はわかりますが、ド・モルガンの証明は案外難しいです。

--proofCheck lemma3 0
--proofCheck lemma3 1
--proofCheck lemma3 2
--proofCheck lemma3 3
--proofCheck lemma3 4
--proofCheck lemma3 5
--proofCheck lemma3 6
--proofCheck lemma3 7
--proofCheck lemma3 8
--proofCheck lemma3 9
--proofCheck lemma3 10
--proofCheck lemma3 11
--を実行するといずれもTrueなので、この証明は正しい。

