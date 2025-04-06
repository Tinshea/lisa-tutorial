package it.unive.lisa.tutorial;

import it.unive.lisa.AnalysisException;
import it.unive.lisa.DefaultConfiguration;
import it.unive.lisa.LiSA;
import it.unive.lisa.analysis.heap.pointbased.FieldSensitivePointBasedHeap;
import it.unive.lisa.analysis.nonrelational.value.ValueEnvironment;
import it.unive.lisa.conf.LiSAConfiguration;
import it.unive.lisa.imp.IMPFrontend;
import it.unive.lisa.imp.ParsingException;
import it.unive.lisa.interprocedural.ReturnTopPolicy;
import it.unive.lisa.program.Program;
import org.junit.Test;

import static org.junit.Assert.assertNotNull;

public class TwoVarInequalityAndFloatCartesianTest {
    @Test
    public void testExtendedSignsTVPIProduct() throws ParsingException, AnalysisException {
        // Parse the program to get the CFG representation
        Program program = IMPFrontend.processFile("inputs/cartesian_test.imp");

        // Build a new configuration for the analysis
        LiSAConfiguration conf = new DefaultConfiguration();

        // Specify where files should be generated
        conf.workdir = "outputs/cartesiantest";

        // Specify the visual format of the analysis results
        conf.analysisGraphs = LiSAConfiguration.GraphType.HTML;

        // Specify the analysis to execute
        conf.abstractState = DefaultConfiguration.simpleState(
                DefaultConfiguration.defaultHeapDomain(),
                new TwoVarInequalityAndFloatCartesian(
                        new TwoVarLinearInequality(),
                        new ValueEnvironment<>(new SetOfFloatValuesWithOverflow(5))
                ),
                DefaultConfiguration.defaultTypeDomain());

        // Instantiate LiSA with the configuration
        LiSA lisa = new LiSA(conf);

        // Run the analysis
        lisa.run(program);

        // Ensure the program is not null after parsing
        assertNotNull(program);
    }
}