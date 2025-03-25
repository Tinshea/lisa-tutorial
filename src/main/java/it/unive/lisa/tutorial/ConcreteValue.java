package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.Lattice;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.SemanticOracle;
import it.unive.lisa.analysis.nonrelational.value.BaseNonRelationalValueDomain;
import it.unive.lisa.analysis.nonrelational.value.ValueEnvironment;
import it.unive.lisa.program.cfg.ProgramPoint;
import it.unive.lisa.symbolic.value.Constant;
import it.unive.lisa.symbolic.value.ValueExpression;
import it.unive.lisa.symbolic.value.Variable;
import it.unive.lisa.symbolic.value.operator.AdditionOperator;
import it.unive.lisa.symbolic.value.operator.DivisionOperator;
import it.unive.lisa.symbolic.value.operator.MultiplicationOperator;
import it.unive.lisa.symbolic.value.operator.SubtractionOperator;
import it.unive.lisa.symbolic.value.operator.binary.BinaryOperator;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonEq;
import it.unive.lisa.util.representation.StringRepresentation;
import it.unive.lisa.util.representation.StructuredRepresentation;

public class ConcreteValue implements BaseNonRelationalValueDomain<ConcreteValue> {
    public static final ConcreteValue BOTTOM = new ConcreteValue(Integer.MIN_VALUE), TOP = new ConcreteValue(Integer.MIN_VALUE);

    private final int value;

    private ConcreteValue(int value) {
        this.value = value;
    }

    @Override
    public ConcreteValue lubAux(ConcreteValue concreteValue) throws SemanticException {
        if(this.value == concreteValue.value)
            return concreteValue;
        else return top();
    }

    @Override
    public boolean lessOrEqualAux(ConcreteValue concreteValue) throws SemanticException {
        return this.value == concreteValue.value;
    }

    @Override
    public ConcreteValue top() {
        return TOP;
    }

    @Override
    public ConcreteValue bottom() {
        return BOTTOM;
    }

    @Override
    public StructuredRepresentation representation() {
        if(this.isBottom())
            return Lattice.bottomRepresentation();
        if(this.isTop())
            return Lattice.topRepresentation();
        return new StringRepresentation(String.valueOf(value));
    }

    @Override
    public ConcreteValue evalNonNullConstant(Constant constant, ProgramPoint pp, SemanticOracle oracle) throws SemanticException {
        if(constant.getValue() instanceof Integer)
            return new ConcreteValue((Integer) constant.getValue());
        return BaseNonRelationalValueDomain.super.evalNonNullConstant(constant, pp, oracle);
    }

    @Override
    public ConcreteValue evalBinaryExpression(BinaryOperator operator, ConcreteValue left, ConcreteValue right, ProgramPoint pp, SemanticOracle oracle) throws SemanticException {
        if(operator instanceof AdditionOperator) {
            if(left.isTop() || right.isTop())
                return top();
            if(left.isBottom() || right.isBottom())
                return bottom();
            return new ConcreteValue(left.value + right.value);
        }
        if(operator instanceof SubtractionOperator) {
            if(left.isTop() || right.isTop())
                return top();
            if(left.isBottom() || right.isBottom())
                return bottom();
            return new ConcreteValue(left.value - right.value);
        }
        if(operator instanceof MultiplicationOperator) {
            if(left.isTop() || right.isTop()) {
                if(left.isTop() && right.value==0)
                    return new ConcreteValue(0);
                else if(right.isTop() && left.value==0)
                    return new ConcreteValue(0);
                else return top();
            }
            if(left.isBottom() || right.isBottom())
                return bottom();
            return new ConcreteValue(left.value * right.value);
        }
        if(operator instanceof DivisionOperator) {
            if(left.isTop() || right.isTop())
                return top();
            if(left.isBottom() || right.isBottom())
                return bottom();
            return new ConcreteValue(left.value / right.value);
        }
        return BaseNonRelationalValueDomain.super.evalBinaryExpression(operator, left, right, pp, oracle);
    }

    @Override
    public ValueEnvironment<ConcreteValue> assumeBinaryExpression(ValueEnvironment<ConcreteValue> environment, BinaryOperator operator, ValueExpression left, ValueExpression right, ProgramPoint src, ProgramPoint dest, SemanticOracle oracle) throws SemanticException {
        if(operator instanceof ComparisonEq && left instanceof Variable)
            return assumeVariableEqualExpression(environment, (Variable) left, right, src, oracle);
        if(operator instanceof ComparisonEq && right instanceof Variable)
            return assumeVariableEqualExpression(environment, (Variable) right, left, src, oracle);
        return BaseNonRelationalValueDomain.super.assumeBinaryExpression(environment, operator, left, right, src, dest, oracle);
    }

    private ValueEnvironment<ConcreteValue> assumeVariableEqualExpression(ValueEnvironment<ConcreteValue> environment, Variable left, ValueExpression right, ProgramPoint src, SemanticOracle oracle) throws SemanticException {
        Variable a = left;
        ConcreteValue v = this.eval(right, environment, src, oracle);
        if(! v.isTop() && ! v.isBottom()) {
            int value = v.value;
            return environment.putState(a, new ConcreteValue(value));
        }
        return environment;
    }
}
