COQC := coqc

all : SfLib.vo ImpDep.vo Equiv.vo ILogic.vo ILTac.vo SepAlg.vo ILInsts.vo BILogic.vo SepAlgMap.vo BILTac.vo ILImp.vo

clean:
	rm -r *.vo
	rm -r *.glob

SfLib.vo: SfLib.v
	$(COQC) SfLib.v

ImpDep.vo: ImpDep.v
	$(COQC) ImpDep.v

Equiv.vo: Equiv.v
	$(COQC) Equiv.v

ILogic.vo: ILogic.v
	$(COQC) ILogic.v

ILTac.vo: ILTac.v
	$(COQC) ILTac.v

SepAlg.vo: SepAlg.v
	$(COQC) SepAlg.v

BILogic.vo: BILogic.v
	$(COQC) BILogic.v

SepAlgMap.vo: SepAlgMap.v
	$(COQC) SepAlgMap.v

ILInsts.vo: ILInsts.v
	$(COQC) ILInsts.v

BILTac.vo: BILTac.v
	$(COQC) BILTac.v

ILImp.vo: ILImp.v
	$(COQC) ILImp.v