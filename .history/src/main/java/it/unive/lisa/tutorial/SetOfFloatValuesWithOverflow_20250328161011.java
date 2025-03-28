package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.Lattice;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.SemanticOracle;
import it.unive.lisa.analysis.lattices.Satisfiability;
import it.unive.lisa.analysis.nonrelational.value.BaseNonRelationalValueDomain;
import it.unive.lisa.analysis.nonrelational.value.ValueEnvironment;
import it.unive.lisa.program.cfg.ProgramPoint;
import it.unive.lisa.symbolic.value.*;
import it.unive.lisa.symbolic.value.operator.AdditionOperator;
import it.unive.lisa.symbolic.value.operator.DivisionOperator;
import it.unive.lisa.symbolic.value.operator.MultiplicationOperator;
import it.unive.lisa.symbolic.value.operator.SubtractionOperator;
import it.unive.lisa.symbolic.value.operator.binary.BinaryOperator;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonLt;
import it.unive.lisa.util.representation.StringRepresentation;
import it.unive.lisa.util.representation.StructuredRepresentation;

import java.util.*;

public class SetOfFloatValuesWithOverflow implements BaseNonRelationalValueDomain<SetOfFloatValuesWithOverflow> {

    private final int maxNumberOfElements;
    private final Set<Float> values;

    public static final SetOfFloatValuesWithOverflow TOP = new SetOfFloatValuesWithOverflow((Set<Float>) null);
    public static final SetOfFloatValuesWithOverflow BOTTOM = new SetOfFloatValuesWithOverflow(new HashSet<>());

    private SetOfFloatValuesWithOverflow(Set<Float> values) {
        this.values = values;
        this.maxNumberOfElements = 5; // valeur par défaut
    }

    public SetOfFloatValuesWithOverflow(float value) {
        this.values = new HashSet<>();
        this.values.add(value);
        this.maxNumberOfElements = 5; // valeur par défaut
    }

    public SetOfFloatValuesWithOverflow(int maxCardinality) {
        this.values = new HashSet<>();
        this.maxNumberOfElements = maxCardinality;
    }

    @Override
    public SetOfFloatValuesWithOverflow top() {
        return TOP;
    }

    @Override
    public SetOfFloatValuesWithOverflow bottom() {
        return BOTTOM;
    }

    public boolean isTop() {
        return this == TOP;
    }

    public boolean isBottom() {
        return this == BOTTOM;
    }

    @Override
    public StructuredRepresentation representation() {
        if (this.isBottom())
            return Lattice.bottomRepresentation();
        if (this.isTop())
            return Lattice.topRepresentation();
        return new StringRepresentation(Arrays.toString(values.toArray()));
    }

    @Override
    public SetOfFloatValuesWithOverflow lubAux(SetOfFloatValuesWithOverflow other) {
        if (this.isTop() || other.isTop())
            return TOP;
        Set<Float> union = new HashSet<>(this.values);
        union.addAll(other.values);
        return union.size() > maxNumberOfElements ? TOP : new SetOfFloatValuesWithOverflow(union);
    }

    @Override
    public boolean lessOrEqualAux(SetOfFloatValuesWithOverflow other) {
        if (other.isTop()) return true;
        if (this.isTop()) return false;
        return other.values.containsAll(this.values);
    }

    @Override
    public SetOfFloatValuesWithOverflow evalNonNullConstant(Constant constant, ProgramPoint pp, SemanticOracle oracle) throws SemanticException {
        if (constant.getValue() instanceof Float) {
            float val = (Float) constant.getValue();
            if (Float.isInfinite(val) || Float.isNaN(val))
                return TOP;
            return new SetOfFloatValuesWithOverflow(val);
        }
        return BaseNonRelationalValueDomain.super.evalNonNullConstant(constant, pp, oracle);
    }

    @Override
    public SetOfFloatValuesWithOverflow evalBinaryExpression(BinaryOperator operator, SetOfFloatValuesWithOverflow left, SetOfFloatValuesWithOverflow right, ProgramPoint pp, SemanticOracle oracle) throws SemanticException {
        if (left.isTop() || right.isTop())
            return TOP;
        if (left.isBottom() || right.isBottom())
            return BOTTOM;
        
        Set<Float> result = new HashSet<>();
        
        if (operator instanceof AdditionOperator) {
            for (Float l : left.values)
                for (Float r : right.values) {
                    float res = l + r;
                    if (Float.isInfinite(res) || Float.isNaN(res))
                        return TOP;
                    result.add(res);
                }
        } else if (operator instanceof SubtractionOperator) {
            for (Float l : left.values)
                for (Float r : right.values) {
                    float res = l - r;
                    if (Float.isInfinite(res) || Float.isNaN(res))
                        return TOP;
                    result.add(res);
                }
        } else if (operator instanceof MultiplicationOperator) {
            for (Float l : left.values)
                for (Float r : right.values) {
                    float res = l * r;
                    if (Float.isInfinite(res) || Float.isNaN(res))
                        return TOP;
                    result.add(res);
                }
        } else if (operator instanceof DivisionOperator) {
            for (Float l : left.values)
                for (Float r : right.values) {
                    if (r == 0.0f)
                        return BOT; // Division par zéro
                    float res = l / r;
                    if (Float.isInfinite(res) || Float.isNaN(res))
                        return TOP;
                    result.add(res);
                }
        } else {
            return BaseNonRelationalValueDomain.super.evalBinaryExpression(operator, left, right, pp, oracle);
        }
        
        return result.size() > maxNumberOfElements ? TOP : new SetOfFloatValuesWithOverflow(result);
    }

    @Override
    public Satisfiability satisfiesBinaryExpression(BinaryOperator operator, SetOfFloatValuesWithOverflow left, SetOfFloatValuesWithOverflow right, ProgramPoint pp, SemanticOracle oracle) throws SemanticException {
        if (left.isTop() || right.isTop())
            return Satisfiability.UNKNOWN;
        if (operator instanceof ComparisonLt) {
            for (Float i : left.values)
                for (Float j : right.values)
                    if (!(i < j))
                        return Satisfiability.UNKNOWN;
            return Satisfiability.SATISFIED;
        }
        return BaseNonRelationalValueDomain.super.satisfiesBinaryExpression(operator, left, right, pp, oracle);
    }

    @Override
    public ValueEnvironment<SetOfFloatValuesWithOverflow> assumeBinaryExpression(ValueEnvironment<SetOfFloatValuesWithOverflow> environment, BinaryOperator operator, ValueExpression left, ValueExpression right, ProgramPoint src, ProgramPoint dest, SemanticOracle oracle) throws SemanticException {
        if (operator instanceof ComparisonLt && left instanceof Variable && right instanceof Constant) {
            Variable x = (Variable) left;
            Constant y = (Constant) right;
            if (y.getValue() instanceof Float) {
                SetOfFloatValuesWithOverflow vals = environment.getState(x);
                if (vals.isTop())
                    return environment;
                Set<Float> filtered = new HashSet<>();
                for (Float v : vals.values)
                    if (v < (Float) y.getValue())
                        filtered.add(v);
                environment.putState(x, new SetOfFloatValuesWithOverflow(filtered));
                return environment;
            }
        }
        return BaseNonRelationalValueDomain.super.assumeBinaryExpression(environment, operator, left, right, src, dest, oracle);
    }
}
