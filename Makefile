MAKEFILE=Makeprime
PROJECT_FILE=_CoqProject

all:
	rocq makefile -f $(PROJECT_FILE) -o $(MAKEFILE)
	$(MAKE) -f $(MAKEFILE)

clean:
	rm *.vo*
	rm *.glob
	rm *.aux
