######################################################
ORG=ucsd-cse230-wi19
ASGN=hw4
######################################################

hw2: deps src/Hw4.hs 
	stack exec -- liquid -i src src/Hw3.hs 

deps: src/ProofCombinators.hs src/State.hs
	stack exec -- liquid -i src src/ProofCombinators.hs
	stack exec -- liquid -i src src/State.hs 
	stack exec -- liquid -i src src/Expressions.hs 

tags:
	hasktags -x -c src/

turnin: 
	git commit -a -m "turnin"
	git push origin master

upstream:
	git remote add upstream git@github.com:$(ORG)/$(ASGN).git

update:
	git pull upstream master
