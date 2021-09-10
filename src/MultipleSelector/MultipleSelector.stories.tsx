import { useState } from 'react';
import { storiesOf } from "@storybook/react";
import MultipleSelector, { Props, Choice } from "./MultipleSelector";
import { words } from '../../.storybook/const';

const choices: Choice[] = words.map((word) => ({ label: word, id: word }));

const defaultProps: Props = {
  label: '',
    popUpKey: 'Mul-Selector-key',
    choiceSections: [{ choices }],
    name: 'Choice',
    placeholder: 'please select choices',
    id: 'Mul-Selector-id',
    handleSelect: ({ value, name }) => { console.log({ value, name })},
    style: { width: '300px' }
};

storiesOf("Multiple Selector", module)
  .add("Normal Multiple Selector", () => {
    function Parent({ children }: { children: any }) {
      const [checkedChoices, setCheckedChoices] = useState<Choice[]>([]);
      return <div>{children(checkedChoices, setCheckedChoices)}</div>;
    }
    return (
      <Parent>
        {(checkedChoices: Choice[], setCheckedChoices: (value: Choice[]) => void) => (
          <MultipleSelector 
            {...defaultProps}
            label={(checkedChoices.length <= 1) ? checkedChoices[0]?.label || '' : `${checkedChoices[0]?.label} & ${checkedChoices.length - 1} More`}
            checkedChoicess={checkedChoices}
            handleSelect={({ value }: { value: Choice[]}) => { setCheckedChoices(value); }}
          />
        )}
      </Parent>
    );
  })
  .add("Multiple Selector With Single Choice", () => {
    function Parent({ children }: { children: any }) {
      const [checkedChoices, setCheckedChoices] = useState<Choice[]>([]);
      return <div>{children(checkedChoices, setCheckedChoices)}</div>;
    }
    return (
      <Parent>
        {(checkedChoices: Choice[], setCheckedChoices: (value: Choice[]) => void) => (
          <MultipleSelector 
            {...defaultProps}
            label={(checkedChoices.length <= 1) ? checkedChoices[0]?.label || '' : `${checkedChoices[0]?.label} & ${checkedChoices.length - 1} More`}
            checkedChoicess={checkedChoices}
            handleSelect={({ value }: { value: Choice[]}) => { setCheckedChoices(value); }}
            choiceSections={[{ sectionName: 'Single Choice', choices: [{ label: 'Special One', singleChoice: true }]}, { sectionName: 'Multiple Choice', choices: choices }]}
          />
        )}
      </Parent>
    );
  })
  .add("Multiple Selector With Section Prefix", () => {
    function Parent({ children }: { children: any }) {
      const [checkedChoices, setCheckedChoices] = useState<Choice[]>([]);
      return <div>{children(checkedChoices, setCheckedChoices)}</div>;
    }
    return (
      <Parent>
        {(checkedChoices: Choice[], setCheckedChoices: (value: Choice[]) => void) => (
          <MultipleSelector 
            {...defaultProps}
            label={(checkedChoices.length <= 1) ? checkedChoices[0]?.label || '' : `${checkedChoices[0]?.label} & ${checkedChoices.length - 1} More`}
            checkedChoicess={checkedChoices}
            handleSelect={({ value }: { value: Choice[]}) => { setCheckedChoices(value); }}
            choiceSections={[{ sectionName: 'Single Choice', sectionPrefix: 'single-prefix', choices: [{ label: 'Special One', singleChoice: true }]}, { sectionName: 'Multiple Choice', choices: choices, sectionPrefix: 'mul-prefix' }]}
          />
        )}
      </Parent>
    );
  })
  .add("Selector With Used Choices", () => {
    function Parent({ children }: { children: any }) {
      const [checkedChoices, setCheckedChoices] = useState<Choice[]>([]);
      return <div>{children(checkedChoices, setCheckedChoices)}</div>;
    }
    return (
      <Parent>
        {(checkedChoices: Choice[], setCheckedChoices: (value: Choice[]) => void) => (
          <MultipleSelector 
            {...defaultProps}
            label={(checkedChoices.length <= 1) ? checkedChoices[0]?.label || '' : `${checkedChoices[0]?.label} & ${checkedChoices.length - 1} More`}
            checkedChoicess={checkedChoices}
            handleSelect={({ value }: { value: Choice[]}) => { setCheckedChoices(value); }}
            choiceSections={[{ choices: words.map((word, index) => ({ label: word, id: word, used: index < 10 })) }]}
          />
        )}
      </Parent>
    );
  })



