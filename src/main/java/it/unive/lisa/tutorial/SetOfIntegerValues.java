package it.unive.lisa.tutorial;

import it.unive.lisa.analysis.Lattice;
import it.unive.lisa.analysis.SemanticException;
import it.unive.lisa.analysis.SemanticOracle;
import it.unive.lisa.analysis.lattices.Satisfiability;
import it.unive.lisa.analysis.nonrelational.value.BaseNonRelationalValueDomain;
import it.unive.lisa.analysis.nonrelational.value.ValueEnvironment;
import it.unive.lisa.program.cfg.ProgramPoint;
import it.unive.lisa.symbolic.value.Constant;
import it.unive.lisa.symbolic.value.ValueExpression;
import it.unive.lisa.symbolic.value.Variable;
import it.unive.lisa.symbolic.value.operator.AdditionOperator;
import it.unive.lisa.symbolic.value.operator.binary.BinaryOperator;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonLe;
import it.unive.lisa.symbolic.value.operator.binary.ComparisonLt;
import it.unive.lisa.util.representation.StringRepresentation;
import it.unive.lisa.util.representation.StructuredRepresentation;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Set;

public class SetOfIntegerValues implements BaseNonRelationalValueDomain<SetOfIntegerValues> {
    private static final int MAX_NUMBER_OF_ELEMENTS = 5;
    private Set<Integer> values;

    private SetOfIntegerValues(Set<Integer> values) {
        this.values = values;
    }

    private SetOfIntegerValues(int value) {
        this.values = new HashSet<>();
        this.values.add(value);
    }

    @Override
    public SetOfIntegerValues lubAux(SetOfIntegerValues setOfIntegerValues) throws SemanticException {
        HashSet<Integer> newValues = new HashSet<>(this.values);
        newValues.addAll(setOfIntegerValues.values);
        if(newValues.size() > MAX_NUMBER_OF_ELEMENTS)
            return top();
        return new SetOfIntegerValues(newValues);
    }

    @Override
    public boolean lessOrEqualAux(SetOfIntegerValues setOfIntegerValues) throws SemanticException {
        return setOfIntegerValues.values.containsAll(this.values);
    }

    public static final SetOfIntegerValues TOP = new SetOfIntegerValues(null);

    @Override
    public SetOfIntegerValues top() {
        return TOP;
        /*HashSet<Integer> result = new HashSet<>();
        for(int i = Integer.MIN_VALUE; i < Integer.MAX_VALUE; i++) {
            result.add(i);
        }
        return new SetOfIntegerValues(result);*/
    }

    private static final SetOfIntegerValues BOTTOM = new SetOfIntegerValues(new HashSet<>());

    @Override
    public SetOfIntegerValues bottom() {
        return BOTTOM;
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
    public SetOfIntegerValues evalNonNullConstant(Constant constant, ProgramPoint pp, SemanticOracle oracle) throws SemanticException {
        if (constant.getValue() instanceof Integer)
            return new SetOfIntegerValues((Integer) constant.getValue());
        return BaseNonRelationalValueDomain.super.evalNonNullConstant(constant, pp, oracle);
    }


    @Override
    public SetOfIntegerValues evalBinaryExpression(BinaryOperator operator, SetOfIntegerValues left, SetOfIntegerValues right, ProgramPoint pp, SemanticOracle oracle) throws SemanticException {
        if (operator instanceof AdditionOperator) {
            if (left.isTop() || right.isTop())
                return top();
            if (left.isBottom() || right.isBottom())
                return bottom();
            HashSet<Integer> newValues = new HashSet<>();
            for (Integer i : left.values)
                for (Integer j : right.values)
                    newValues.add(i + j);
            return new SetOfIntegerValues(newValues);
        }
        return BaseNonRelationalValueDomain.super.evalBinaryExpression(operator, left, right, pp, oracle);
    }

    @Override
    public Satisfiability satisfiesBinaryExpression(BinaryOperator operator, SetOfIntegerValues left, SetOfIntegerValues right, ProgramPoint pp, SemanticOracle oracle) throws SemanticException {
        if(left.isTop() || right.isTop() )
            return Satisfiability.UNKNOWN;
        if(operator instanceof ComparisonLt) {
            for(Integer i : left.values)
                for(Integer j : right.values)
                    if(! (i < j))
                        return Satisfiability.UNKNOWN;
            return Satisfiability.SATISFIED;
        }
        return BaseNonRelationalValueDomain.super.satisfiesBinaryExpression(operator, left, right, pp, oracle);
    }

    @Override
    //left operator right
    public ValueEnvironment<SetOfIntegerValues> assumeBinaryExpression(ValueEnvironment<SetOfIntegerValues> environment, BinaryOperator operator, ValueExpression left, ValueExpression right, ProgramPoint src, ProgramPoint dest, SemanticOracle oracle) throws SemanticException {
        if(operator instanceof ComparisonLt && left instanceof Variable && right instanceof Constant) {
            Variable x = (Variable) left;
            Constant y = (Constant) right;
            if(y.getValue() instanceof Integer) {
                SetOfIntegerValues vals = environment.getState(x);
                if(vals.isTop())
                    return environment;
                HashSet<Integer> possibleValues = new HashSet<>();
                for(Integer i : vals.values)
                    if(i < (Integer) y.getValue())
                        possibleValues.add(i);
                environment.putState(x, new SetOfIntegerValues(possibleValues));
                return environment;
            }
        }
        return BaseNonRelationalValueDomain.super.assumeBinaryExpression(environment, operator, left, right, src, dest, oracle);
    }
}