const path = require('path');

const chai = require('chai');
const chaiAsPromised = require('chai-as-promised');
const yeomanHelpers = require('yeoman-test');
const expect = chai.expect;

chai.use(chaiAsPromised);

const promises = require('../../util/promises.js');

describe('NUnit', function () {
	let generatedTestSuite;

	before(function () {
		const fixture = require(path.join(__dirname, '../fixtures/inputs/SimpleMath.json'));

		return yeomanHelpers.run(path.join(__dirname, '../../generators/app'))
			.inDir('test/tmp/nunit/')
			.withOptions({
				model: JSON.stringify(fixture),
				framework: 'nunit'
			}).then(() => {
				return promises.fsReadFile('build/SimpleMathTest.cs');
			}).then((data) => {
				generatedTestSuite = data;
			});
	});

	it('should make a test suite for SimpleMath', function () {
		expect(generatedTestSuite).to.exist;
	});

	it('should have a test setUp', function () {
		expect(generatedTestSuite).to.have.string('[TestInitialize]');
		expect(generatedTestSuite).to.have.string('Initialize');
		expect(generatedTestSuite).to.have.string('SimpleMath testee');
		expect(generatedTestSuite).to.have.string('testee = new SimpleMath()');
	});

	it('should have 3 tests for Add', function () {
		const match = generatedTestSuite.match(/test_Add/g);

		expect(match).to.have.length(3);
	});

	it('should have 3 tests for Subtract', function () {
		const match = generatedTestSuite.match(/test_Subtract/g);

		expect(match).to.have.length(3);
	});

	it('should have 3 tests for Divide', function () {
		const match = generatedTestSuite.match(/test_Divide/g);

		expect(match).to.have.length(3);
	});

	it('should have 2 tests for SquareRoot', function () {
		const match = generatedTestSuite.match(/test_SquareRoot/g);

		expect(match).to.have.length(2);
	});

	it('should have converted "Integer" to "int"', function () {
		expect(generatedTestSuite).to.match(/int/);
		expect(generatedTestSuite).to.not.match(/Integer/);
	});

	after(function () {
		// Reset location due to changing from helpers running in specific directory.
		process.chdir('../../../');
	});
});
