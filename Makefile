all: 
	 coqc projet.v

clean:
	rm -f *.vo 
	rm -f *.glob
	rm -f *~
