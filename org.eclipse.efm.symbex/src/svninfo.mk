
SVNINFO_BAK = svninfo.bak
SVNINFO_NEW = svninfo.tmp

AVM_LAUNCHER_CPP = `pwd`/../src/main/AvmLauncher.cpp


all: AvmLauncher.cpp

AvmLauncher.cpp: svninfo
	@if test -s $(SVNINFO_NEW); \
	then \
	  rm -f $(SVNINFO_NEW); \
	  SVN_REV=`cat $(SVNINFO_BAK) | egrep "^R.vision.:" | egrep -o "[[:digit:]]+$$"`; \
	  SVN_REV_NEXT=$$(($$SVN_REV + 1 )); \
	  echo "SUBVERSION_REVISION = $$SVN_REV_NEXT" ; \
	  sed -i -r -e "50,70 s/(SUBVERSION_REVISION_NUMBER) = [0-9]+/\1 = $${SVN_REV_NEXT}/" \
	            -e "50,70 s/(SUBVERSION_REVISION_STRING) = \"[0-9]+\"/\1 = \"$${SVN_REV_NEXT}\"/" $(AVM_LAUNCHER_CPP) ; \
	fi

svninfo: svninfo-gen
	@if test -s $(SVNINFO_BAK); \
	then \
	  if diff -q $(SVNINFO_NEW) $(SVNINFO_BAK) > /dev/null ; \
	  then rm -f $(SVNINFO_NEW); echo "No difference !"; \
	  else cp $(SVNINFO_NEW) $(SVNINFO_BAK); echo "Update of $(SVNINFO_BAK)"; \
	  fi; \
	else cp $(SVNINFO_NEW) $(SVNINFO_BAK); echo "Creation of $(SVNINFO_BAK)"; \
	fi

# .PHONY ensures the .tmp version is always rebuilt (to check for any changes)
.PHONY: svninfo-gen
svninfo-gen:
	svn info `pwd`/../src > $(SVNINFO_NEW)


