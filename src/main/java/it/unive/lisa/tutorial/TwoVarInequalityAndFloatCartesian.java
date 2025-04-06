package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.combination.CartesianProduct;
import it.unive.lisa.analysis.nonrelational.value.ValueEnvironment;
import it.unive.lisa.analysis.value.ValueDomain;
import it.unive.lisa.symbolic.value.Identifier;
import it.unive.lisa.symbolic.value.ValueExpression;

public class TwoVarInequalityAndFloatCartesian
        extends CartesianProduct<
        TwoVarInequalityAndFloatCartesian,
        TwoVarLinearInequality,
        ValueEnvironment<SetOfFloatValuesWithOverflow>,
        ValueExpression,
        Identifier>
        implements ValueDomain<TwoVarInequalityAndFloatCartesian> {

    public TwoVarInequalityAndFloatCartesian(
            TwoVarLinearInequality left,
            ValueEnvironment<SetOfFloatValuesWithOverflow> right
    ) {
        super(left, right);
    }

    @Override
    public boolean knowsIdentifier(Identifier id) {
        return left.knowsIdentifier(id) || right.knowsIdentifier(id);
    }

    @Override
    public TwoVarInequalityAndFloatCartesian mk(TwoVarLinearInequality left, ValueEnvironment<SetOfFloatValuesWithOverflow> right) {
        return new TwoVarInequalityAndFloatCartesian(left, right);
    }
}
