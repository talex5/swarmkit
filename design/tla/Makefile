WORKERS := 4

.PHONY: all check pdfs tlaps

all: check pdfs tlaps

# Run the TLC+ model checker
check:
	# XXX: TLC doesn't return non-zero on error!!
	#docker run --rm -it --workdir /mnt -v ${PWD}:/mnt talex5/tla java tlc2.TLC -workers ${WORKERS} SwarmKit.tla -config models/SwarmKit.cfg
	docker run --rm -it --workdir /mnt -v ${PWD}:/mnt talex5/tla java tlc2.TLC -workers ${WORKERS} WorkerImpl.tla -config models/WorkerImpl.cfg

# Run the TLAPS proof checker
tlaps:
	docker run --rm -it --workdir /mnt -v ${PWD}:/mnt talex5/tla tlapm -I /usr/local/lib/tlaps SwarmKit.tla

# Generate a PDF file from a .tla file
%.pdf: %.tla
	[ -d metadir ] || mkdir metadir
	docker run --rm -it --workdir /mnt -v ${PWD}:/mnt talex5/tla java tla2tex.TLA -shade -latexCommand pdflatex -latexOutputExt pdf -metadir metadir $<

pdfs: SwarmKit.pdf Types.pdf Tasks.pdf WorkerSpec.pdf EventCounter.pdf
