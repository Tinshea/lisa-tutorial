package it.unive.lisa.tutorial;

import it.unive.lisa.AnalysisException;
import it.unive.lisa.DefaultConfiguration;
import it.unive.lisa.LiSA;
import it.unive.lisa.analysis.nonrelational.value.ValueEnvironment;
import it.unive.lisa.conf.LiSAConfiguration;
import it.unive.lisa.conf.LiSAConfiguration.GraphType;
import it.unive.lisa.imp.IMPFrontend;
import it.unive.lisa.imp.ParsingException;
import it.unive.lisa.interprocedural.ReturnTopPolicy;
import it.unive.lisa.program.Program;
import org.junit.Test;

public class SetOfFloatValuesWithOverflowTest {

	@Test
	public void testFloatDomain() throws ParsingException, AnalysisException {
		// Parse the IMP file from the inputs folder
		Program program = IMPFrontend.processFile("inputs/setoffloatvalueswithoverflow.imp");

		// Configure LiSA
		LiSAConfiguration conf = new DefaultConfiguration();
		conf.workdir = "outputs/setoffloatvalueswithoverflow";
		conf.analysisGraphs = GraphType.HTML;

		// Use our custom domain
		SetOfFloatValuesWithOverflow domain = new SetOfFloatValuesWithOverflow(5);
		conf.abstractState = DefaultConfiguration.simpleState(
				DefaultConfiguration.defaultHeapDomain(),
				new ValueEnvironment<>(domain),
				DefaultConfiguration.defaultTypeDomain());

		conf.openCallPolicy = ReturnTopPolicy.INSTANCE;

		// Run the analysis
		LiSA lisa = new LiSA(conf);
		lisa.run(program);
	}
}
