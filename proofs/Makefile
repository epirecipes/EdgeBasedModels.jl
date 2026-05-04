.PHONY: build mdgen html pdf clean all

PANDOC_FLAGS = --standalone --toc --mathjax \
    --css=style.css \
    --metadata title="Categorical Foundations of Edge-Based Compartmental Models" \
    --metadata author="Simon Frost" \
    --syntax-highlighting=tango

# Order matches EBCMCategory.lean imports (dependency order)
MD_FILES = \
    EpiCategory.md CoarseGrain.md GaloisPair.md \
    Obstructions.md Hierarchy.md DynamicLimits.md SurvivalBridge.md \
    ClosureTheorem.md MessagePassingBridge.md ClusteringExtension.md MethodOfStages.md \
    DegreeCorrelation.md ConvergenceTheorems.md CategoricalComposition.md

all: build mdgen html

# Build the Lean 4 project (verifies all proofs)
build:
	lake build

# Generate markdown from Lean source via mdgen
mdgen:
	rm -rf .mdgen_tmp
	mkdir -p .mdgen_tmp
	lake exe mdgen EBCMCategory .mdgen_tmp
	cat $(addprefix .mdgen_tmp/, $(MD_FILES)) > EBCMCategory.md
	rm -rf .mdgen_tmp
	@echo "Generated EBCMCategory.md"

# Generate HTML from markdown
html: EBCMCategory.md
	pandoc EBCMCategory.md -o EBCMCategory.html $(PANDOC_FLAGS)
	@echo "Generated EBCMCategory.html"

# Generate PDF from markdown
pdf: EBCMCategory.md
	pandoc EBCMCategory.md -o EBCMCategory.pdf \
	    --pdf-engine=lualatex \
	    --toc \
	    --metadata title="Categorical Foundations of Edge-Based Compartmental Models" \
	    --metadata author="Simon Frost" \
	    --syntax-highlighting=tango \
	    -H header.tex
	@echo "Generated EBCMCategory.pdf"

clean:
	rm -f EBCMCategory.html EBCMCategory.pdf EBCMCategory.md
	rm -rf .mdgen_tmp
