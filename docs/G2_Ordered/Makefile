all:
	@pdflatex Language #> /dev/null
	@bibtex   Language
	@pdflatex Language #> /dev/null
	@pdflatex Language
	@echo Done
clean:
	@rm *.aux *.log *.bbl *.blg
	@echo Clean
clean-all: 
	@rm *.pdf *.aux *.log *.bbl *.blg
	@echo Cleaned-All