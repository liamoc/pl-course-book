LATEXMK=latexmk
LATEXMKARGS=-pdf
JUNK=$(shell echo `cat .gitignore`)
STYLE_FILES=$(shell ls -b *.sty)
UNIV_DEPS=preamble.tex $(STYLE_FILES)
CHAPTERS=$(shell ls -b ch*.tex | sed "s/\.tex//g") 

all: book

$(CHAPTERS): %: %.tex $(UNIV_DEPS)
	$(LATEXMK) $(LATEXMKARGS) $@.tex  

book: gitHeadInfo.gin main.tex $(UNIV_DEPS)
	$(LATEXMK) $(LATEXMKARGS) main.tex

gitHeadInfo.gin: 
	./gen_gitinfo.sh  
clean: 
	rm -rf $(JUNK)


