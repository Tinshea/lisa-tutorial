package it.unive.lisa.tutorial;

import it.unive.lisa.AnalysisException;
import it.unive.lisa.DefaultConfiguration;
import it.unive.lisa.LiSA;
import it.unive.lisa.analysis.heap.pointbased.FieldSensitivePointBasedHeap;
import it.unive.lisa.analysis.nonrelational.value.ValueEnvironment;
import it.unive.lisa.conf.LiSAConfiguration;
import it.unive.lisa.conf.LiSAConfiguration.GraphType;
import it.unive.lisa.imp.IMPFrontend;
import it.unive.lisa.imp.ParsingException;
import it.unive.lisa.program.Program;
import org.junit.Test;
import static org.junit.Assert.assertNotNull;




public class TwoVarLinearInequalityTest {

    @Test
    public void testBasicAnalysis() throws ParsingException, AnalysisException {
        // Parse the program to get the CFG representation
        Program program = IMPFrontend.processFile("inputs/TwoVarLinearInequality.imp");

        // Build a new configuration for the analysis
        LiSAConfiguration conf = new DefaultConfiguration();

        // Specify where files should be generated
        conf.workdir = "outputs/twovarlinearinequality";

        // Specify the visual format of the analysis results
        conf.analysisGraphs = GraphType.HTML;

        // Specify the analysis to execute
        conf.abstractState = DefaultConfiguration.simpleState(
                new FieldSensitivePointBasedHeap(),
                new TwoVarLinearInequality(),
                DefaultConfiguration.defaultTypeDomain());

        // Instantiate LiSA with the configuration
        LiSA lisa = new LiSA(conf);

        // Run the analysis
        lisa.run(program);

        // Ensure the program is not null after parsing
        assertNotNull(program);
    }

}