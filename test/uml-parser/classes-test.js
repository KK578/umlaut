const chai = require('chai');
const expect = chai.expect;

const testee = require('../../uml-parser/util/classes.js');
let TestClass;

describe('UML Parser Classes', () => {
	describe('AnnotatedUmlClass', () => {
		before(() => {
			TestClass = testee.AnnotatedUmlClass;
		});

		it('should error on empty input', () => {
			expect(() => {
				new TestClass();
			}).to.throw(Error);
		});

		it('should take a name', () => {
			const obj = new TestClass('foo');

			// expect(obj.id).to.be.a('string').and.not.equal('');
			expect(obj.name).to.equal('foo');
		});

		it('should define hashmaps after initialisation', () => {
			const obj = new TestClass('foo');

			expect(obj.variables).to.be.an('object');
			expect(obj.methods).to.be.an('object');
			expect(obj.invariants).to.be.an('object');
		});

		describe('#addVariable', () => {
			let obj;

			beforeEach(() => {
				obj = new TestClass('foo');
			});

			it('should error on empty input', () => {
				expect(obj.addVariable).to.throw(Error);
			});

			it('should take a name', () => {
				obj.addVariable('a');

				expect(obj.variables).to.include.keys('a');
				expect(obj.variables['a']).to.include({ type: 'object' });
			});

			it('should take a name and type', () => {
				obj.addVariable('a', 'Integer');

				expect(obj.variables).to.include.keys('a');
				expect(obj.variables['a']).to.include({ type: 'Integer' });
			});

			it('should error if variable name already exists', () => {
				obj.addVariable('a', 'Integer');

				expect(obj.variables).to.include.keys('a');
				expect(obj.variables['a']).to.include({ type: 'Integer' });

				expect(obj.addVariable.bind(obj, 'a', 'Integer')).to.throw(Error);
			});
		});

		describe('#addMethod', () => {
			let obj;

			beforeEach(() => {
				obj = new TestClass('foo');
			});

			it('should error on empty input', () => {
				expect(obj.addMethod).to.throw(Error);
			});

			it('should error with just name', () => {
				expect(obj.addMethod.bind(obj, 'foo')).to.throw(Error);
			});

			it('should take a name and type', () => {
				const methodsLength = Object.keys(obj.methods).length;

				obj.addMethod('foo', 'Integer');

				expect(Object.keys(obj.methods).length).to.equal(methodsLength + 1);
				expect(obj.methods).to.include.keys('foo');
			});

			it('should take a name and type and list of arguments', () => {
				obj.addMethod('foo', 'Integer', [{ a: { type: 'Integer' } }]);

				expect(obj.methods).to.include.keys('foo');
				expect(obj.methods['foo'].type).equal('Integer');
				expect(obj.methods['foo'].args).to.include({ a: { type: 'Integer' } });
			});

			it('should error if list of arguments is not an Array', () => {
				expect(obj.addMethod.bind(obj, 'foo', 'Integer', 'a')).to.throw(Error);
			});

			it('should error if method name already exists', () => {
				obj.addMethod('foo', 'Integer');

				// Validate method is added.
				expect(obj.methods).to.include.keys('foo');

				// Test adding method again.
				expect(obj.addMethod.bind(obj, 'foo', 'Integer')).to.throw(Error);
			});
		});

		describe('#addInvariant', () => {
			let obj;

			beforeEach(() => {
				obj = new TestClass('foo');
			});

			it('should error on empty', () => {
				expect(obj.addInvariant).to.throw(Error);
			});

			it('should error if argument is not an object', () => {
				expect(obj.addInvariant.bind(obj, '(> a b)')).to.throw(Error);
			});

			it('should add a new invariant', () => {
				const invariantLength = Object.keys(obj.invariants).length;

				obj.addInvariant({
					comparison: 'LessThan',
					args: [
						'a',
						'b'
					]
				});

				expect(Object.keys(obj.invariants).length).to.equal(invariantLength + 1);
			});

			it('should error if invariant object does not specify the comparison', () => {
				expect(obj.addInvariant.bind(obj, {
					comparison: undefined,
					args: [
						'a',
						'b'
					]
				})).to.throw(Error);
			});

			it('should error if invariant object does not specify at least 1 item in arguments', () => {
				expect(obj.addInvariant.bind(obj, {
					comparison: 'LessThan',
					args: []
				})).to.throw(Error);
			});

			it('should generate a unique ID for the condition');
		});
	});

	describe('UmlAnnotatedMethod', () => {
		before(() => {
			TestClass = testee.AnnotatedUmlMethod;
		});

		it('should error on empty input', () => {
			expect(() => {
				new TestClass();
			}).to.throw(Error);
		});

		it('should error with just name', () => {
			expect(() => {
				new TestClass('foo');
			}).to.throw(Error);
		});

		it('should take a name and type', () => {
			const obj = new TestClass('foo', 'Integer');

			expect(obj.name).to.equal('foo');
			expect(obj.type).to.equal('Integer');
		});

		it('should take a name and type and list of arguments', () => {
			const obj = new TestClass('foo', 'Integer', [{ a: { type: 'Integer' } }]);

			expect(obj.name).to.equal('foo');
			expect(obj.type).to.equal('Integer');
			expect(obj.args).to.include({ a: { type: 'Integer' } });
		});

		it('should error if list of arguments is not an array', () => {
			expect(() => {
				new TestClass('foo', 'Integer', 'a');
			}).to.throw(Error);
		});

		it('should define hashmaps after initialisation', () => {
			const obj = new TestClass('foo', 'Integer');

			expect(obj.preconditions).to.be.an('object');
			expect(obj.postconditions).to.be.an('object');
		});

		describe('#setType', () => {
			let obj;

			beforeEach(() => {
				obj = new TestClass('foo', 'Integer');
			});

			it('should error on empty', () => {
				expect(obj.setType).to.throw(Error);
			});

			it('should take a type name', () => {
				expect(obj.type).to.not.equal('String');

				obj.setType('String');

				expect(obj.type).to.equal('String');
			});
		});

		describe('#addArgument', () => {
			let obj;

			beforeEach(() => {
				obj = new TestClass('foo', 'Integer');
			});

			it('should error on empty', () => {
				expect(obj.addArgument).to.throw(Error);
			});

			it('should add a new argument, as an object', () => {
				obj.addArgument({
					name: 'a',
					type: 'Integer'
				});

				expect(obj.args).to.include({
					name: 'a',
					type: 'Integer'
				});
			});

			it('should error if argument object does not have a name', () => {
				expect(obj.addArgument.bind(obj, { type: 'Integer' })).to.throw(Error);
			});

			it('should error if argument object does not have a type', () => {
				expect(obj.addArgument.bind(obj, { name: 'a' })).to.throw(Error);
			});

			it('should error if argument name already exists in that method', () => {
				obj.addArgument({
					name: 'a',
					type: 'Integer'
				});

				// Validate the argument now exists.
				expect(obj.args).to.include({
					name: 'a',
					type: 'Integer'
				});

				expect(obj.addArgument.bind(obj, {
					name: 'a',
					type: 'Integer'
				})).to.throw(Error);
			});
		});

		describe('#addPrecondition', () => {
			let obj;

			beforeEach(() => {
				obj = new TestClass('foo', 'Integer');
			});

			it('should error on empty', () => {
				expect(obj.addPrecondition).to.throw(Error);
			});

			it('should error if argument is not an object', () => {
				expect(obj.addPrecondition.bind(obj, '(> a b)')).to.throw(Error);
			});

			it('should add a new precondition', () => {
				const preconditionsLength = Object.keys(obj.preconditions).length;

				obj.addPrecondition({
					comparison: 'LessThan',
					args: [
						'a',
						'b'
					]
				});

				expect(Object.keys(obj.preconditions).length).to.equal(preconditionsLength + 1);
			});

			it('should error if precondition object does not specify the comparison', () => {
				expect(obj.addPrecondition.bind(obj, {
					comparison: undefined,
					args: [
						'a',
						'b'
					]
				})).to.throw(Error);
			});

			it('should error if precondition object does not specify at least 1 item in arguments', () => {
				expect(obj.addPrecondition.bind(obj, {
					comparison: 'LessThan',
					args: []
				})).to.throw(Error);
			});

			it('should generate a unique ID for the condition');
		});

		describe('#addPostcondition', () => {
			let obj;

			beforeEach(() => {
				obj = new TestClass('foo', 'Integer');
			});

			it('should error on empty', () => {
				expect(obj.addPostcondition).to.throw(Error);
			});

			it('should error if argument is not an object', () => {
				expect(obj.addPostcondition.bind(obj, '(> a b)')).to.throw(Error);
			});

			it('should add a new postcondition', () => {
				const postconditionsLength = Object.keys(obj.postconditions).length;

				obj.addPostcondition({
					comparison: 'LessThan',
					args: [
						'a',
						'b'
					]
				});

				expect(Object.keys(obj.postconditions).length).to.equal(postconditionsLength + 1);
			});

			it('should error if postcondition object does not specify the comparison', () => {
				expect(obj.addPostcondition.bind(obj, {
					comparison: undefined,
					args: [
						'a',
						'b'
					]
				})).to.throw(Error);
			});

			it('should error if postcondition object does not specify at least 1 item in arguments', () => {
				expect(obj.addPostcondition.bind(obj, {
					comparison: 'LessThan',
					args: []
				})).to.throw(Error);
			});

			it('should generate a unique ID for the condition');
		});
	});

	describe('OclCondition', () => {
		before(() => {
			TestClass = testee.OclCondition;
		});

		it('should error on empty', () => {
			expect(() => {
				new TestClass();
			}).to.throw(Error);
		});

		it('should error if condition is not an object', () => {
			expect(() => {
				new TestClass('(> a b)');
			}).to.throw(Error);
		});

		it('should take a condition object', () => {
			const obj = new TestClass({
				comparison: 'LessThan',
				args: [
					'a',
					'b'
				]
			});

			expect(obj.comparison).to.equal('LessThan');
			expect(obj.args).to.include('a').and.include('b');
			expect(obj.isInverted).to.not.be.ok;
		});

		it('should error if condition does not have a comparison', () => {
			expect(() => {
				new TestClass({
					comparison: undefined,
					args: [
						'a',
						'b'
					]
				});
			}).to.throw(Error);
		});

		it('should error if condition is not an Array', () => {
			expect(() => {
				new TestClass({
					comparison: 'GreaterThan',
					args: 'a, b'
				});
			}).to.throw(Error);
		});

		it('should error if condition does not have at least one argument', () => {
			expect(() => {
				new TestClass({
					comparison: 'GreaterThan',
					args: []
				});
			}).to.throw(Error);
		});

		it('should set isInverted value in object', () => {
			const obj = new TestClass({
				comparison: 'LessThan',
				args: [
					'a',
					'b'
				],
				isInverted: true
			});

			expect(obj.comparison).to.equal('LessThan');
			expect(obj.args).to.include('a').and.include('b');
			expect(obj.isInverted).to.be.ok;
		});

		describe('#setInverted', () => {
			let obj;

			beforeEach(() => {
				obj = new TestClass({
					comparison: 'LessThan',
					args: [
						'a',
						'b'
					]
				});
			});

			it('should error on empty input', () => {
				expect(obj.setInverted).to.throw(Error);
			});

			it('should error if value is not a boolean', () => {
				expect(obj.setInverted.bind(obj, 'true')).to.throw(Error);
			});

			it('should set isInverted flag to value', () => {
				// Validate change occurs due to method call.
				expect(obj.isInverted).to.be.not.ok;

				obj.setInverted(true);

				expect(obj.isInverted).to.be.ok;
			});
		});

		describe('#setException', () => {
			let obj;

			beforeEach(() => {
				obj = new TestClass({
					comparison: 'LessThan',
					args: [
						'a',
						'b'
					]
				});
			});

			it('should error on empty', () => {
				expect(obj.setException).to.throw(Error);
			});

			it('should take type name for an Exception', () => {
				expect(obj.exception).to.be.undefined;

				obj.setException('NullException');

				expect(obj.exception).to.include({ type: 'NullException' });
			});
		});
	});
});
