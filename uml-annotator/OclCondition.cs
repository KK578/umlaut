using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Text.RegularExpressions;
using System.Threading.Tasks;

namespace UmlAnnotator
{
	public class OclCondition
	{
		public OclComparison Comparator { get; set; }
		private List<string> arguments;
		private string exception;
		private bool isInverted;

		public OclCondition()
		{
			arguments = new List<string>();
		}

		public OclCondition(string condition)
		{
			string innerCondition = condition;
			if (innerCondition.StartsWith("("))
			{
				innerCondition = innerCondition.Substring(1, innerCondition.Length - 2);
			}

			string[] items = innerCondition.Split(' ');
			// Ternary ensures inversion syntax is handled correctly here.
			Comparator = FindComparison(items[1] == "not" ? items[2] : items[1]);

			arguments = new List<string>();
			// Left hand argument is the first.
			arguments.Add(items[0]);
			// Right hand argument is the last.
			arguments.Add(items[items.Length - 1]);
		}

		public void SetArgument(int index, string argument)
		{
			arguments[index] = argument;
		}

		public void SetArguments(string argument)
		{
			arguments = new List<string>(Regex.Split(argument, "\r?\n"));
		}

		public string GetArgument(int index)
		{
			return arguments[index];
		}

		public string GetArgumentsString()
		{
			return String.Join("\r\n", arguments);
		}

		public void SetException(string ex)
		{
			if (!String.IsNullOrWhiteSpace(ex))
			{
				exception = String.Format("Exception:{0}", ex);
			}
			else
			{
				exception = "";
			}
		}

		private OclComparison FindComparison(string comparison)
		{
			// HACK: See MainWindow for explanation.
			List<OclComparison> comparisons = MainWindow.comparisonList;

			foreach (OclComparison c in comparisons)
			{
				if (comparison == c.Symbol)
				{
					return c;
				}
			}

			return null;
		}

		public void SetInverted(bool value)
		{
			if (Comparator.IsInvertable)
			{
				isInverted = value;
			}
		}

		public override string ToString()
		{
			string comparison = "";

			if (Comparator != null)
			{
				comparison = Comparator.Symbol;
			}

			string main = String.Format("{0} {1} {2}", arguments[0], isInverted ? "not " + comparison : comparison, arguments[1]);
			string result;

			if (!String.IsNullOrWhiteSpace(exception))
			{
				result = String.Format("({0} {1})", main, exception);
			}
			else
			{
				result = String.Format("({0})", main);
			}

			return result;
		}
	}
}
